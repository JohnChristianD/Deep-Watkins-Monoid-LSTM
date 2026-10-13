# -*- org -*-
# | ~C-x C-a~ | transform org ~org-agda~ blocks to literate Agda blocs        |
# | ~C-x C-o~ | transform literate Agda code delimiters to org ~org-agda~ src |
#
# Need to ensure org-indent-mode is off when going to agda.
#
# C-c C-= to see constraints.

#+TITLE: A Gentle Introduction to Reflection in Agda
#+DESCRIPTION: How can we use a single proof to prove two different theorems? One proof pattern, multiple invocations!
#+AUTHOR: Musa Al-hassy
#+EMAIL: alhassy@gmail.com
#+STARTUP: indent
#+PROPERTY: header-args :tangle tangled.agda :comments link

#+CATEGORIES: Agda MetaProgramming
#+OPTIONS: html-postamble:nil toc:nil d:nil tag:nil
# IMAGE: ../assets/img/org_logo.png
# SOURCE: https://raw.githubusercontent.com/alhassy/org-agda-mode/master/literate.lagda

# INCLUDE: ~/Dropbox/MyUnicodeSymbols.org

* Abstract       :ignore:
#+BEGIN_CENTER org
*Abstract*
#+END_CENTER

/One proof for two different theorems!/

Let's learn how we can do that in Agda.

This tutorial is the result of mostly experimenting with the
[[https://agda.readthedocs.io/en/v2.5.2/language/reflection.html][documentation]] on Agda's reflection mechanism, which essentially
only exposes the reflection interface and provides a few tiny examples.
The goal of this tutorial is to contain a diverse variety of examples,
along with occasional exercises for the reader.

Examples include:
+ String manipulation of built-in identifier names. 🍓
+ Handy dandy combinators for AST formation: ~𝓋𝓇𝒶, λ𝓋_↦_, …~. 🛠
+ Numerous examples of quotation of terms and types. 🎯
+ Wholesale derivation of singleton types for an example datatype,
  along with derivable proofs 💛 🎵
+ Automating proofs that are only ~refl~ /with/ pattern matching 🏄
+ Discussion of C-style macros in Agda 🌵
+ Abstracting proofs patterns without syntactic overhead using macros 💪 🎼
+ Remarks on what I could not do, possibly since it cannot be done :sob:

Everything here works with Agda version 2.6.0.
This document is a literate Agda file written using
the (poorly coded) [[https://alhassy.github.io/literate/][org-agda]] framework.

A pure ~.agda~ file can be found [[file:tangled.agda][here]].

#+TOC: headlines 2

* Imports
:PROPERTIES:
:header-args: :tangle no
:END:

First, some necessary imports:
\begin{code}
module gentle-intro-to-reflection where

import Level as Level
open import Reflection hiding (name; Type)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Unary using (Decidable)
open import Relation.Nullary

open import Data.Unit
open import Data.Nat as Nat hiding (_⊓_)
open import Data.Bool
open import Data.Product
open import Data.List as List
open import Data.Char as Char
open import Data.String as String
open import Function using (_$_)
\end{code}

:TangledImports:
Repetition is a bad idea, but doing this since org-agda isn't mature
to support blocks with options, such as no tangling.

#+BEGIN_SRC org-agda :tangle "tangled.agda"
module tangled where

import Level as Level
open import Reflection hiding (_≟_ ; name)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Unary using (Decidable)
open import Relation.Nullary

open import Data.Unit
open import Data.Nat  as Nat hiding (_⊓_)
open import Data.Bool
open import Data.Product
open import Data.List as List
open import Data.Char as Char
open import Data.String as String
#+END_SRC
:End:

* Introduction

/Reflection/ is the ability to convert program code into an abstract syntax,
a data structure that can be manipulated like any other.

Consider, for example, the tedium of writing a decidable equality for an enumerated type.
Besides being tedious and error-prone, the inexpressibility of
what should be a mechanically-derivable concept
obscures the corresponding general principle underlying it, thus foregoing
any machine assistance in ensuring any correctness or safety-ness guarantees.
Reflection allows a more economical and disciplined approach.

It is the aim of this tutorial to show how to get started with reflection in Agda.
To the best of my knowledge there is no up to date tutorial on this matter.

There are three main types in Agda's reflection mechanism:
~Name, Arg, Term~. We will learn about them with the aid of
this following simple enumerated typed, as well as other standard types.

\begin{code}
data RGB : Set where
  Red Green Blue : RGB
\end{code}

* Teaser: A Quaint Testing Setup

We shall introduce a convenient syntax for /trivial/ unit tests;
in doing so, we obtain a quick glimpse of the unquotation mechanism in Agda.

:Hide_for_presentation_purposes:
\begin{code}
{- In order to use ~do~-notation we need to have the following definitions in scope. -}
{- These definitions are repeated in the section
    “Metaprogramming with The Typechecking Monad TC”-}

_>>=_        : ∀ {a b} {A : Set a} {B : Set b} → TC A → (A → TC B) → TC B
_>>=_ = bindTC

_>>_        : ∀ {a b} {A : Set a} {B : Set b} → TC A → TC B → TC B
_>>_  = λ p q → p >>= (λ _ → q)
\end{code}
:End:

Agda permits unnamed tests as follows:
\begin{spec}
{- Document what this test shows. -}
_ : ∀ {x1 … xN} → l ≡ r
_ = refl
\end{spec}
To the uninitated, the undescore seems esoteric and a beginner may well prefer
to name their tests ~test₀, test₁, test₂, …~. The latter, while disciplined, is
amicable to the rearranging of the unit tests, say for presentation purposes or
grouping related tests together.

In this section, we solve this two problems: Tests can easily be relocated without
requiring any renaming, and tests grouped due to some relationship are easily identified.

In-particular, the above unit test schema now becomes:
\begin{spec}
unquoteDecl = test  "Document what this test shows."  ∀ {x1 … xN} → l ≡ r
\end{spec}

If we could declare ~test~ as a top-level unquoter, then it's use would be less icky!
For example, it would be nice to have ~syntax~ declarations affect unquotation.

Instead, we declare ~test~ as a normal function yielding results in the ‘type checking’
monad. *Do not worry about the code, it will be sensible after subsequent sections.*
\begin{code}
test : ∀ {ℓ}  (documentation : String) (trivialFact : Set ℓ) → TC ⊤
test _ t =
  do η ← freshName "test-nice"
     τ ← quoteTC t
     declareDef (arg (arg-info visible relevant) η) τ
     defineFun η [ clause [] (con (quote refl) []) ]
\end{code}

Here are some example uses that are orderinr-invariant.
\begin{code}
unquoteDecl = test  "Everything is equal to itself"  ∀ {c : ℕ} → c ≡ c
unquoteDecl = test  "As Russel and Whitehead showed, SS0 is 2" ∀ {c : ℕ} → 1 + 1 ≡ 2
-- unquoteDecl = test (∀ {c : ℕ} → 1 + 1 ≡ 3) "Error: 2 ≠ 3"
\end{code}

Even though it's a bit clumsy, I do prefer it since it avoids the
~_ = refl~ line and replaces ~_ : ⋯~ with the more informative ~test ⋯~.

Morevoer, the reeptition avoided is noticable when we have batch unit tests :grin:
\begin{code}
unquoteDecl =
  do test "Many tests together"     ∀ {c : ℕ} {p : 1 + 1 ≡ 2} → p ≡ p
     -- test "Crashes since a ≠ b"  ∀ {A : Set} {a b : A} → a ≡ b
     test "It's all refl!"          ∀ {A : Set} {a b : A} → a ≡ a
\end{code}

It may seem like all of the above tests produce functions with the same name,
~"test-nice"~, however naming is resolved after the file is loaded and so no
name conflicts transpire. We're making use of a bug, it seems.

Anyhow, I think this is cute (─‿‿─)

Here's some variants.
\begin{code}
{- Handy infix combinator -}
infix 0 _⇨_
_⇨_ = test

{- Alternative, no doc string variant -}
infix 0 testing_
testing_ : ∀ {ℓ}  (trivialFact : Set ℓ) → TC ⊤
testing_ t = test "" t
\end{code}
The ~testing_~ is an ‘operator’ since it explicitly
takes a post-fix argument, and as such the argument
needn't be enclosed with parentheses. Indeed:
\begin{code}
unquoteDecl =
 do test "Needs parenthesis" (1 ≡ 1)
    test "Using ∀-scope" ∀ {_ : ℕ} → 1 ≡ 1

    "Using mixfix" ⇨ 1 ≡ 1

    testing 1 ≡ 1
\end{code}

* ~NAME~ ─Type of known identifiers

~Name~ is the type of quoting identifiers, Agda names.
Elements of this type can be formed and pattern matched using
the ~quote~ keyword.

\begin{code}
a-name : Name
a-name = quote ℕ

isNat : Name → Bool
isNat (quote ℕ) = true
isNat _         = false

-- bad : Set → Name
-- bad s = quote s  {- s is not known -}
\end{code}

+ ~NAME~ comes equipped with equality, ordering, and a show function.
+ Quote will not work on function arguments; the identifier must be known.

Let's show names:
\begin{code}
_ : showName (quote _≡_) ≡ "Agda.Builtin.Equality._≡_"
_ = refl
\end{code}

Or, using our new testing setup:
\begin{code}
unquoteDecl = test "Example Name showing" (showName (quote _≡_) ≡ "Agda.Builtin.Equality._≡_")
\end{code}
This may not be pretty, but it will be when we have many related tests ;-)

#+BEGIN_SRC org-agda :tangle nil
_ : showName (quote Red) ≡ "gentle-intro-to-reflection.RGB.Red"
_ = refl
#+END_SRC

It would be nice to have ~Red~ be shown as just ~“RGB.Red”~.

First, let's introduce some ‘programming’ helpers to treat Agda strings as if they
where Haskell strings, and likewise to treat predicates as decidables.
\begin{code}
{- Like “$” but for strings. -}
_⟨𝒮⟩_ : (List Char → List Char) → String → String
f ⟨𝒮⟩ s = fromList (f (toList s))

{- This should be in the standard library; I could not locate it. -}
toDec : ∀ {ℓ} {A : Set ℓ} → (p : A → Bool) → Decidable {ℓ} {A} (λ a → p a ≡ true)
toDec p x with p x
toDec p x | false = no λ ()
toDec p x | true = yes refl
\end{code}

We can now easily obtain the module's name, then drop it from the data constructor's name.
\begin{code}
module-name : String
module-name = takeWhile (toDec (λ c → not (c Char.== '.'))) ⟨𝒮⟩ showName (quote Red)
\end{code}

#+BEGIN_SRC org-agda :tangle nil
_ : module-name ≡ "gentle-intro-to-reflection"
_ = refl
#+END_SRC

\begin{code}
strName : Name → String
strName n = drop (1 + String.length module-name) ⟨𝒮⟩ showName n
{- The “1 +” is for the “.” seperator in qualified names. -}

_ : strName (quote Red) ≡ "RGB.Red"
_ = refl
\end{code}

~NAME~ essentially provides us with the internal representation of a known name,
for which we can query to obtain its definition or type.
Later we will show how to get the type constructors of ~ℕ~ from its name.

* ~Arg~ ─Type of arguments

Arguments in Agda may be hidden or computationally irrelevant.
This information is captured by the ~Arg~ type.

\begin{spec}
{- Arguments can be (visible), {hidden}, or ⦃instance⦄ -}
data Visibility : Set where
  visible hidden instance′ : Visibility

{-Arguments can be relevant or irrelevant: -}
data Relevance : Set where
  relevant irrelevant : Relevance

{- Visibility and relevance characterise the behaviour of an argument: -}
data ArgInfo : Set where
  arg-info : (v : Visibility) (r : Relevance) → ArgInfo

data Arg (A : Set) : Set where
  arg : (i : ArgInfo) (x : A) → Arg A
\end{spec}

For example, let's create some helpers that make arguments of any given type ~A~:
\begin{code}
{- 𝓋isible 𝓇elevant 𝒶rgument -}
𝓋𝓇𝒶 : {A : Set} → A → Arg A
𝓋𝓇𝒶 = arg (arg-info visible relevant)

{- 𝒽idden 𝓇elevant 𝒶rgument -}
𝒽𝓇𝒶 : {A : Set} → A → Arg A
𝒽𝓇𝒶 = arg (arg-info hidden relevant)
\end{code}

Below are the variable counterparts, for the ~Term~ datatype,
which will be discussed shortly.
+ Variables are De Bruijn indexed and may be applied to a list of arguments.
+ The index /n/ refers to the argument that is /n/ locations away from ‘here’.

\begin{code}
{- 𝓋isible 𝓇elevant 𝓋ariable -}
𝓋𝓇𝓋 : (debruijn : ℕ) (args : List (Arg Term)) → Arg Term
𝓋𝓇𝓋 n args = arg (arg-info visible relevant) (var n args)

{- 𝒽idden 𝓇elevant 𝓋ariable -}
𝒽𝓇𝓋 : (debruijn : ℕ) (args : List (Arg Term)) → Arg Term
𝒽𝓇𝓋 n args = arg (arg-info hidden relevant) (var n args)
\end{code}

* ~Term~ ─Type of terms

We use the ~quoteTerm~ keyword to turn a well-typed fragment of code
---concrete syntax--- into a value of the ~Term~ datatype ---the abstract syntax.
Here's the definition of ~Term~:
\begin{spec}
data Term where

  {- A variable has a De Bruijn index and may be applied to arguments. -}
  var       : (x : ℕ)  (args : List (Arg Term)) → Term

  {- Constructors and definitions may be applied to a list of arguments. -}
  con       : (c : Name) (args : List (Arg Term)) → Term
  def       : (f : Name) (args : List (Arg Term)) → Term

  {- λ-abstractions bind one varaible; “t” is the string name of the variable
    along with the body of the lambda.
  -}
  lam       : (v : Visibility) (t : Abs Term) → Term  {- Abs A  ≅  String × A -}
  pat-lam   : (cs : List Clause) (args : List (Arg Term)) → Term

  {- Telescopes, or function types; λ-abstraction for types. -}
  pi        : (a : Arg Type) (b : Abs Type) → Term

  {- “Set n” or some term that denotes a type -}
  agda-sort : (s : Sort) → Term

  {- Metavariables; introduced via quoteTerm -}
  meta      : (x : Meta) → List (Arg Term) → Term

  {- Literal  ≅  ℕ | Word64 | Float | Char | String | Name | Meta -}
  lit       : (l : Literal) → Term

  {- Items not representable by this AST; e.g., a hole. -}
  unknown   : Term {- Treated as '_' when unquoting. -}

data Sort where
  set     : (t : Term) → Sort {- A Set of a given (possibly neutral) level. -}
  lit     : (n : Nat) → Sort  {- A Set of a given concrete level. -}
  unknown : Sort

data Clause where
  clause        : (ps : List (Arg Pattern)) (t : Term) → Clause
  absurd-clause : (ps : List (Arg Pattern)) → Clause
\end{spec}

** Example: Simple Types

Here are three examples of “def”ined names, the first two do not take an argument.
The last takes a visible and relevant argument, 𝓋𝓇𝒶, that is a literal natural.
\begin{code}

unquoteDecl
  = do "AST representation of ℕ"  ⇨  quoteTerm ℕ ≡ def (quote ℕ) []
       "Empty List" ⇨ quoteTerm List.List ≡ def (quote List.List) []
       "Parameterised datatype"
         ⇨ quoteTerm (List.List ℕ) ≡ def (quote List.List) (𝓋𝓇𝒶 (quoteTerm ℕ) ∷ [])
\end{code}
If we did not use the testing framework, even without comments, we would
need more lines for these trivial tests:
\begin{code}
_ : quoteTerm ℕ ≡ def (quote ℕ) []
_ = refl

_ : quoteTerm List ≡ def (quote List) []
_ = refl

_ : quoteTerm (List ℕ) ≡ def (quote List) (𝓋𝓇𝒶 (quoteTerm ℕ) ∷ [])
_ = refl
\end{code}

** Example: Simple Terms

Elementary numeric quotations:
\begin{code}
unquoteDecl =
  do
     "Literal" ⇨ quoteTerm 1 ≡ lit (nat 1)

     "Constructors"
       ⇨    quoteTerm (suc zero)
          ≡ con (quote suc)
            (arg (arg-info visible relevant) (quoteTerm zero) ∷ [])



_ : quoteTerm 1 ≡ lit (nat 1)
_ = refl

_ :    quoteTerm (suc zero)
     ≡ con (quote suc) (arg (arg-info visible relevant) (quoteTerm zero) ∷ [])
_ = refl

{- Using our helper 𝓋𝓇𝒶 -}
_ : quoteTerm (suc zero) ≡ con (quote suc) (𝓋𝓇𝒶 (quoteTerm zero) ∷ [])
_ = refl
\end{code}

The first example below demonstrates that ~true~ is a type “con”structor
that takes no arguments, whence the ~[]~. The second example shows that
~_≡_~ is a defined name, not currently applied to any arguments.
The final example has propositional equality applied to two arguments.
\begin{code}
_ : quoteTerm true ≡ con (quote true) []
_ = refl

_ : quoteTerm _≡_ ≡ def (quote _≡_) []
_ = refl

_ :   quoteTerm ("b" ≡ "a")
    ≡ def (quote _≡_)
      ( 𝒽𝓇𝒶 (def (quote Level.zero) [])
      ∷ 𝒽𝓇𝒶 (def (quote String) [])
      ∷ 𝓋𝓇𝒶 (lit (string "b"))
      ∷ 𝓋𝓇𝒶 (lit (string "a")) ∷ [])
_ = refl
\end{code}

Notice that a propositional equality actually has four arguments ─a level, a type, and two arguments─
where the former two happen
to be inferrable from the latter.
Here is a more polymorphic example:
\begin{code}
_ : ∀ {level : Level.Level}{Type : Set level} (x y : Type)
    →   quoteTerm (x ≡ y)
       ≡ def (quote _≡_)
           (𝒽𝓇𝓋 3 [] ∷ 𝒽𝓇𝓋 2 [] ∷ 𝓋𝓇𝓋 1 [] ∷ 𝓋𝓇𝓋 0 [] ∷ [])

_ = λ x y → refl
\end{code}
Remember that a De Bruijn index ~n~ refers to the lambda variable
that is ~n+1~ lambdas away from its use site.
For example, ~𝓋𝓇𝓋 1~ means starting at the ~⋯ ≡ ⋯~, go ~1+1~
lambdas away to get the variable ~x~.

We will demonstrate an example of a section, say
~≡_ "b"~, below when discussing lambda abstractions.

** A relationship between ~quote~ and ~quoteTerm~

Known names ~𝒻~ in a quoted term are denoted by a ~quote 𝒻~ in the AST representation.

For example ─I will use this 𝒻ℴ𝓃𝓉 for my postulated items─
\begin{code}
postulate 𝒜 ℬ : Set
postulate 𝒻 : 𝒜 → ℬ
_ : quoteTerm 𝒻 ≡ def (quote 𝒻) []
_ = refl
\end{code}

In contrast, names that /vary/ are denoted by a ~var~ constructor in the AST representation.
\begin{code}
module _ {A B : Set} {f : A → B} where
  _ : quoteTerm f ≡ var 0 []
  _ = refl
\end{code}

** Example: Lambda Terms

First we show how reduction with lambdas works then we show how lambda functions
are represented as ~Term~ values.

~quoteTerm~ typechecks and normalises its argument before yielding a ~Term~ value.
\begin{code}
_ : quoteTerm ((λ x → x) "nice") ≡ lit (string "nice")
_ = refl
\end{code}

Eta-reduction happens, ~f ≈ λ x → f x~.
\begin{code}
id : {A : Set} → A → A
id x = x

_ :   quoteTerm (λ (x : ℕ) → id x)
    ≡ def (quote id) (𝒽𝓇𝒶 (def (quote ℕ) []) ∷ [])
_ = refl
\end{code}

No delta-reduction happens; function definitions are not elaborated.
\begin{code}
_ :   quoteTerm (id "a")
    ≡ def (quote id)
        (𝒽𝓇𝒶 (def (quote String) []) ∷  𝓋𝓇𝒶 (lit (string "a")) ∷ [])
_ = refl
\end{code}

Here is a simple identity function on the Booleans.
A “lam”bda with a “visible” “abs”tract argument named ~"x"~ is introduced
having as body merely being the 0 nearest-bound variable, applied to an empty
list of arguments.
\begin{code}
_ : quoteTerm (λ (x : Bool) → x) ≡ lam visible (abs "x" (var 0 []))
_ = refl

\end{code}

Here is a more complicated lambda abstraction: Note that ~f a~ is represented as
the variable 0 lambdas away from the body applied to the variable 1 lambda away
from the body.
\begin{code}
_ : quoteTerm (λ (a : ℕ) (f : ℕ → ℕ) → f a)
    ≡  lam visible (abs "a"
         (lam visible (abs "f"
           (var 0 (arg (arg-info visible relevant) (var 1 []) ∷ [])))))
_ = refl
\end{code}

This is rather messy, let's introduce some syntactic sugar to make it more readable.
\begin{code}
infixr 5 λ𝓋_↦_  λ𝒽_↦_

λ𝓋_↦_  λ𝒽_↦_ : String → Term → Term
λ𝓋 x ↦ body  = lam visible (abs x body)
λ𝒽 x ↦ body  = lam hidden (abs x body)
\end{code}
Now the previous example is a bit easier on the eyes:
\begin{code}
_ :   quoteTerm (λ (a : ℕ) (f : ℕ → ℕ) → f a)
    ≡ λ𝓋 "a" ↦ λ𝓋 "f" ↦ var 0 [ 𝓋𝓇𝒶 (var 1 []) ]
_ = refl
\end{code}

Using that delicious sugar, let's look at the constant function a number of ways.
\begin{code}
_ : {A B : Set} →   quoteTerm (λ (a : A) (b : B) → a)
                  ≡ λ𝓋 "a" ↦ (λ𝓋 "b" ↦ var 1 [])
_ = refl

_ :  quoteTerm (λ {A B : Set} (a : A) (_ : B) → a)
    ≡ (λ𝒽 "A" ↦ (λ𝒽 "B" ↦ (λ𝓋 "a" ↦ (λ𝓋 "_" ↦ var 1 []))))
_ = refl

const : {A B : Set} → A → B → A
const a _ = a

_ : quoteTerm const ≡ def (quote const) []
_ = refl
\end{code}

Finally, here's an example of a section.
\begin{code}
_ :   quoteTerm (_≡ "b")
    ≡ λ𝓋 "section" ↦
       (def (quote _≡_)
        (𝒽𝓇𝒶 (def (quote Level.zero) []) ∷
         𝒽𝓇𝒶 (def (quote String) []) ∷
         𝓋𝓇𝒶 (var 0 []) ∷
         𝓋𝓇𝒶 (lit (string "b")) ∷ []))
_ = refl
\end{code}

* Metaprogramming with The Typechecking Monad ~TC~
The ~TC~ monad provides an interface to Agda's type checker.
\begin{spec}
postulate
  TC       : ∀ {a} → Set a → Set a
  returnTC : ∀ {a} {A : Set a} → A → TC A
  bindTC   : ∀ {a b} {A : Set a} {B : Set b} → TC A → (A → TC B) → TC B
\end{spec}

In order to use ~do~-notation we need to have the following definitions in scope.
\begin{spec}
_>>=_        : ∀ {a b} {A : Set a} {B : Set b} → TC A → (A → TC B) → TC B
_>>=_ = bindTC

_>>_        : ∀ {a b} {A : Set a} {B : Set b} → TC A → TC B → TC B
_>>_  = λ p q → p >>= (λ _ → q)
\end{spec}
#
# “spec” since these definitions were activated earlier in the testing framework.
# But it's only sensible to show them here in the presentation.

The primitives of ~TC~ can be seen on the [[https://agda.readthedocs.io/en/v2.6.0/language/reflection.html#type-checking-computations][documentation]] page; below are a few notable
ones that we may use. Other primitives include support for the current context,
type errors, and metavariables.
\begin{spec}
postulate
  {- Take what you have and try to make it fit into the current goal. -}
  unify : (have : Term) (goal : Term) → TC ⊤

  {- Try first computation, if it crashes with a type error, try the second. -}
  catchTC : ∀ {a} {A : Set a} → TC A → TC A → TC A

  {- Infer the type of a given term. -}
  inferType : Term → TC Type

  {- Check a term against a given type. This may resolve implicit arguments
     in the term, so a new refined term is returned. Can be used to create
     new metavariables: newMeta t = checkType unknown t -}
  checkType : Term → Type → TC Term

  {- Compute the normal form of a term. -}
  normalise : Term → TC Term

  {- Quote a value, returning the corresponding Term. -}
  quoteTC : ∀ {a} {A : Set a} → A → TC Term

  {- Unquote a Term, returning the corresponding value. -}
  unquoteTC : ∀ {a} {A : Set a} → Term → TC A

  {- Create a fresh name. -}
  freshName : String → TC Name

  {- Declare a new function of the given type. The function must be defined
     later using 'defineFun'. Takes an Arg Name to allow declaring instances
     and irrelevant functions. The Visibility of the Arg must not be hidden. -}
  declareDef : Arg Name → Type → TC ⊤

  {- Define a declared function. The function may have been declared using
     'declareDef' or with an explicit type signature in the program. -}
  defineFun : Name → List Clause → TC ⊤

  {- Get the type of a defined name. Replaces 'primNameType'. -}
  getType : Name → TC Type

  {- Get the definition of a defined name. Replaces 'primNameDefinition'. -}
  getDefinition : Name → TC Definition

  {-  Change the behaviour of inferType, checkType, quoteTC, getContext
      to normalise (or not) their results. The default behaviour is no
      normalisation. -}
  withNormalisation : ∀ {a} {A : Set a} → Bool → TC A → TC A
\end{spec}

~TC~ computations, or “metaprograms”, can be run by declaring them as macros or by
unquoting. Let's begin with the former.

* Unquoting ─Making new functions & types

Recall our ~RGB~ example type was a simple enumeration consisting of ~Red, Green, Blue~.
Consider the singleton type:
\begin{spec}
data IsRed : RGB → Set where
  yes : IsRed Red
\end{spec}
The name ~Red~ completely determines this datatype; so let's try to generate it
mechanically. Unfortunately, as far as I could tell, there is currently no way
to unquote ~data~ declarations. As such, we'll settle for the following
isomorphic functional formulation:
\begin{spec}
IsRed : RGB → Set
IsRed x = x ≡ Red
\end{spec}

First, let's quote the relevant parts, for readability.
\begin{code}
“ℓ₀” : Arg Term
“ℓ₀” = 𝒽𝓇𝒶 (def (quote Level.zero) [])

“RGB” : Arg Term
“RGB” = 𝒽𝓇𝒶 (def (quote RGB) [])

“Red” : Arg Term
“Red” = 𝓋𝓇𝒶 (con (quote Red) [])
\end{code}
The first two have a nearly identical definition and it would be nice to
mechanically derive them...

Anyhow,
we use the ~unquoteDecl~ keyword, which allows us to obtain a ~NAME~ value, ~IsRed~.
We then quote the desired type, declare a function of that type, then define it
using the provided ~NAME~.
\begin{code}
unquoteDecl IsRed =
  do ty ← quoteTC (RGB → Set)
     declareDef (𝓋𝓇𝒶 IsRed) ty
     defineFun IsRed   [ clause [ 𝓋𝓇𝒶 (var "x") ] (def (quote _≡_) (“ℓ₀” ∷ “RGB” ∷ “Red” ∷ 𝓋𝓇𝓋 0 [] ∷ [])) ]
\end{code}
Let's try out our newly declared type.
\begin{code}
red-is-a-solution : IsRed Red
red-is-a-solution = refl

green-is-not-a-solution : ¬ (IsRed Green)
green-is-not-a-solution = λ ()

red-is-the-only-solution : ∀ {c} → IsRed c → c ≡ Red
red-is-the-only-solution refl = refl
\end{code}

There is a major problem with using ~unquoteDef~ outright like this:
We cannot step-wise refine our program using holes ~?~, since that would
result in unsolved meta-variables. Instead, we split this process into two stages:
A programming stage, then an unquotation stage.

\begin{code}
{- Definition stage, we can use ‘?’ as we form this program. -}
define-Is : Name → Name → TC ⊤
define-Is is-name qcolour = defineFun is-name
  [ clause [ 𝓋𝓇𝒶 (var "x") ] (def (quote _≡_) (“ℓ₀” ∷ “RGB” ∷ 𝓋𝓇𝒶 (con qcolour []) ∷ 𝓋𝓇𝓋 0 [] ∷ [])) ]

declare-Is : Name → Name → TC ⊤
declare-Is is-name qcolour =
  do let η = is-name
     τ ← quoteTC (RGB → Set)
     declareDef (𝓋𝓇𝒶 η) τ
     defineFun is-name
       [ clause [ 𝓋𝓇𝒶 (var "x") ]
         (def (quote _≡_) (“ℓ₀” ∷ “RGB” ∷ 𝓋𝓇𝒶 (con qcolour []) ∷ 𝓋𝓇𝓋 0 [] ∷ [])) ]

{- Unquotation stage -}
IsRed′ : RGB → Set
unquoteDef IsRed′ = define-Is IsRed′ (quote Red)

{- Trying it out -}
_ : IsRed′ Red
_ = refl
\end{code}

Notice that if we use “unquoteDef”, we must provide a type signature.
We only do so for illustration; the next code block avoids such a redundancy by
using “unquoteDecl”.

The above general approach lends itself nicely to the other data constructors as well:
\begin{code}
unquoteDecl IsBlue  = declare-Is IsBlue  (quote Blue)
unquoteDecl IsGreen = declare-Is IsGreen (quote Green)

{- Example use -}
disjoint-rgb  : ∀{c} → ¬ (IsBlue c × IsGreen c)
disjoint-rgb (refl , ())
\end{code}

The next natural step is to avoid manually invoking ~declare-Is~ for each constructor.
Unfortunately, it seems fresh names are not accessible, for some reason. 😢

For example, you would think the following would produce a function
named ~gentle-intro-to-reflection.identity~. Yet, it is not in scope.
I even tried extracting the definition to its own file and no luck.
\begin{code}
unquoteDecl {- identity -}
  = do {- let η = identity -}
       η ← freshName "identity"
       τ ← quoteTC (∀ {A : Set} → A → A)
       declareDef (𝓋𝓇𝒶 η) τ
       defineFun η [ clause [ 𝓋𝓇𝒶 (var "x") ] (var 0 []) ]

{- “identity” is not in scope!?
_ : ∀ {x : ℕ}  →  identity x  ≡  x
_ = refl
-}
\end{code}

*Exercises*:
0. Comment out the ~freshName~ line above and uncomment the surrounding artifacts to so that the above
   unit test goes through.
1. Using that as a template, unquote a function ~everywhere-0 : ℕ → ℕ~ that is constantly 0.
2. Unquote the constant combinator ~K : {A B : Set} → A → B → A~.
\begin{spec}
unquoteDecl everywhere-0
  = do ⋯

_ : everywhere-0 3 ≡ 0
_ = refl

unquoteDecl K
  = do ⋯

_ : K 3 "cat" ≡ 3
_ = refl
\end{spec}

*Bonus:* Proofs of a singleton type such as ~IsRed~ are essentially the same for all singleton types
over ~RGB~. Write, in two stages, a metaprogram that demonstrates each singleton type has a single member
─c.f., ~red-is-the-only-solution~ from above. Hint: This question is as easy as the ones before it.
\begin{spec}
{- Programming stage }
declare-unique : Name → (RGB → Set) → RGB → TC ⊤
declare-unique it S colour =
  = do ⋯

{- Unquotation stage -}
unquoteDecl red-unique = declare-unique red-unique IsRed Red
unquoteDecl green-unique = declare-unique green-unique IsGreen Green
unquoteDecl blue-unique = declare-unique blue-unique IsBlue Blue

{- Test -}
_ : ∀ {c} → IsGreen c → c ≡ Green
_ = green-unique
\end{spec}

:Solutions:
\begin{code}
{- Exercise: -}
unquoteDecl everywhere-0
  = do let η = everywhere-0
       τ ← quoteTC (ℕ → ℕ)
       declareDef (𝓋𝓇𝒶 η) τ
       defineFun η [ clause [ 𝓋𝓇𝒶 (var "x") ] (con (quote zero) []) ]

_ : everywhere-0 3 ≡ 0
_ = refl
{- End -}

{- Exercise: -}
unquoteDecl K
  = do let η = K
       τ ← quoteTC ({A B : Set} → A → B → A)
       declareDef (𝓋𝓇𝒶 η) τ
       defineFun η [ clause (𝓋𝓇𝒶 (var "x") ∷ 𝓋𝓇𝒶 (var "y") ∷ []) (var 1 []) ]

_ : K 3 "cat" ≡ 3
_ = refl
{- End -}

{- Exercise: -}
declare-unique : Name → (RGB → Set) → RGB → TC ⊤
declare-unique it S colour =
  do let η = it
     τ ← quoteTC (∀ {c} → S c → c ≡ colour)
     declareDef (𝓋𝓇𝒶 η) τ
     defineFun η [ clause [ 𝓋𝓇𝒶 (con (quote refl) []) ] (con (quote refl) []) ]

unquoteDecl red-unique = declare-unique red-unique IsRed Red
unquoteDecl green-unique = declare-unique green-unique IsGreen Green
unquoteDecl blue-unique = declare-unique blue-unique IsBlue Blue

_ : ∀ {c} → IsGreen c → c ≡ Green
_ = green-unique
{- End -}
\end{code}
:End:

:Failed_exploration:
\begin{spec}
RGB-constructors : Definition → Name × Name × Name
RGB-constructors (data-type pars (x ∷ y ∷ z ∷ cs)) = x , y , z
RGB-constructors _ = n , n , n where n = quote RGB

unquoteDecl
  =    do δ ← getDefinition (quote RGB)

          let r , g , b = RGB-constructors δ
       -- TODO: get unqualified name, then prefix it with "Is",
       -- then make that into a new name. Then declare a function with that name.

          η ← freshName "IsX"
          -- let η = r
          τ ← quoteTC (RGB → Set)
          declareDef (𝓋𝓇𝒶 η) τ
          define-Is η

-- _ : {!!} -- IsX Red -- gentle-intro-to-reflection.IsX
-- _ = {!IsX!}
--
\end{spec}
:End:

* Sidequest: Avoid tedious ~refl~ proofs

Time for a breather (•̀ᴗ•́)و

Look around your code base for a function that makes explicit pattern matching, such as:
\begin{code}
just-Red : RGB → RGB
just-Red Red   = Red
just-Red Green = Red
just-Red Blue  = Red

only-Blue : RGB → RGB
only-Blue Blue = Blue
only-Blue _   = Blue
\end{code}

Such functions have properties which cannot be proven unless we pattern match
on the arguments they pattern match. For example, that the above function is
constantly ~Red~ requires pattern matching then a ~refl~ for each clause.
\begin{code}
just-Red-is-constant : ∀{c} → just-Red c ≡ Red
just-Red-is-constant {Red}   = refl
just-Red-is-constant {Green} = refl
just-Red-is-constant {Blue}  = refl

{- Yuck, another tedious proof -}
only-Blue-is-constant : ∀{c} → only-Blue c ≡ Blue
only-Blue-is-constant {Blue}  = refl
only-Blue-is-constant {Red}   = refl
only-Blue-is-constant {Green} = refl
\end{code}

In such cases, we can encode the general design decisions ---/pattern match and yield refl/---
then apply the schema to each use case.

Here's the schema:
\begin{code}
constructors : Definition → List Name
constructors (data-type pars cs) = cs
constructors _ = []

by-refls : Name → Term → TC ⊤
by-refls nom thm-you-hope-is-provable-by-refls
 = let mk-cls : Name → Clause
       mk-cls qcolour = clause [ 𝒽𝓇𝒶 (con qcolour []) ] (con (quote refl) [])
   in
   do let η = nom
      δ ← getDefinition (quote RGB)
      let clauses = List.map mk-cls (constructors δ)
      declareDef (𝓋𝓇𝒶 η) thm-you-hope-is-provable-by-refls
      defineFun η clauses
\end{code}

Here's a use case.
\begin{code}
_ : ∀{c} → just-Red c ≡ Red
_ = nice
  where unquoteDecl nice = by-refls nice (quoteTerm (∀{c} → just-Red c ≡ Red))
\end{code}

Note:
0. The first ~nice~ refers to the function
   created by the RHS of the unquote.

1. The RHS ~nice~ refers to the Name value provided
   by the LHS.

2. The LHS ~nice~ is a declaration of a Name value.

This is rather clunky since the theorem to be proven was repeated twice
─repetition is a signal that something's wrong! In the next section we
use macros to avoid such repetiton, as well as the ~quoteTerm~ keyword.

Note that we use a ~where~ clause since unquotation cannot occur in a ~let~,
for some reason.

Here's another use case of the proof pattern (•̀ᴗ•́)و
\begin{code}
_ : ∀{c} → only-Blue c ≡ Blue
_ = nice
  where unquoteDecl nice = by-refls nice (quoteTerm ∀{c} → only-Blue c ≡ Blue)
\end{code}

One proof pattern, multiple invocations!
Super neat stuff :grin:

* Macros ─Abstracting Proof Patterns

 Macros are functions of type ~τ₀ → τ₁ → ⋯ → Term → TC ⊤~ that are defined in a
 ~macro~ block. The last argument is supplied by the type checker and denotes
 the “goal” of where the macro is placed: One generally unifies what they have
 with the goal, what is desired in the use site.

 Why the ~macro~ block?
 + Metaprograms can be run in a term position.
 + Without the macro block, we run computations using the ~unquote~ keyword.
 + Quotations are performed automatically; e.g.,
   if ~f : Term → Name → Bool → Term → TC ⊤~
   then an application ~f u v w~ desugars into
   ~unquote (f (quoteTerm u) (quote v) w)~.

   No syntactic overhead: Macros are applied like normal functions.

Macros cannot be recursive; instead one defines a recursive function outside the
macro block then has the macro call the recursive function.

** C-style macros

In the C language one defines a macro, say, by ~#define luckyNum 1972~ then later uses
it simply by the name ~luckyNum~. Without macros, we have syntactic overhead using
the ~unquote~ keyword:
\begin{code}
luckyNum₀ : Term → TC ⊤
luckyNum₀ h = unify h (quoteTerm 55)

num₀ : ℕ
num₀ = unquote luckyNum₀
\end{code}
Instead, we can achieve C-style behaviour by placing our metaprogramming code within a ~macro~ block.
\begin{code}
macro
  luckyNum : Term → TC ⊤
  luckyNum h = unify h (quoteTerm 55)

num : ℕ
num = luckyNum
\end{code}
Unlike C, all code fragments must be well-defined.

*Exercise:* Write a macro to always yield the first argument in a function.
The second example shows how it can be used to access implicit arguments
without mentioning them :b
\begin{spec}
macro
  first : Term → TC ⊤
  first goal = ⋯

myconst : {A B : Set} → A → B → A
myconst = λ x → λ y → first

mysum : ({x} y : ℕ) → ℕ
mysum y = y + first
\end{spec}
:Solution:
\begin{code}
{- exercise -}
macro
  first : Term → TC ⊤
  first goal = unify goal (var 1 [])

myconst : {A B : Set} → A → B → A
myconst = λ x → λ y → first

mysum : ( {x} y : ℕ) → ℕ
mysum y = y + first
{- end -}
\end{code}
:End:

C-style macros ─unifying against a concretely quoted term─ are helpful
when learning reflection. For example, define a macro ~use~ that yields
different strings according to the shape of their input ─this exercise
increases familiarity with the ~Term~ type. Hint: Pattern match on the
first argument ;-)
\begin{spec}
macro
  use : Term → Term → TC ⊤
  use = ⋯
\end{spec}
:Solution:
\begin{code}
macro
  use : Term → Term → TC ⊤
  use (def _ []) goal = unify goal (quoteTerm "Nice")
  use v goal = unify goal  (quoteTerm "WoahThere")
\end{code}
:End:
\begin{code}
{- Fully defined, no arguments. -}

2+2≈4 : 2 + 2 ≡ 4
2+2≈4 = refl

_ : use 2+2≈4 ≡ "Nice"
_ = refl

{- ‘p’ has arguments. -}

_ : {x y : ℕ} {p : x ≡ y} → use p ≡ "WoahThere"
_ = refl
\end{code}

** Tedious Repetitive Proofs No More!
Suppose we wish to prove that addition, multiplication, and exponentiation
have right units 0, 1, and 1 respectively. We obtain the following nearly identical
proofs!

\begin{code}
+-rid : ∀{n} → n + 0 ≡ n
+-rid {zero}  = refl
+-rid {suc n} = cong suc +-rid

*-rid : ∀{n} → n * 1 ≡ n
*-rid {zero}  = refl
*-rid {suc n} = cong suc *-rid

^-rid : ∀{n} → n ^ 1 ≡ n
^-rid {zero}  = refl
^-rid {suc n} = cong suc ^-rid
\end{code}

There is clearly a pattern here screaming to be abstracted, let's comply ♥‿♥

The natural course of action in a functional language is to try a higher-order combinator:
\begin{code}
{- “for loops” or “Induction for ℕ” -}
foldn : (P : ℕ → Set) (base : P zero) (ind : ∀ n → P n → P (suc n))
      → ∀(n : ℕ) → P n
foldn P base ind zero    = base
foldn P base ind (suc n) = ind n (foldn P base ind n)
\end{code}

Now the proofs are shorter:
\begin{code}
_ : ∀ (x : ℕ) → x + 0 ≡ x
_ = foldn _ refl (λ _ → cong suc)    {- This and next two are the same -}

_ : ∀ (x : ℕ) → x * 1 ≡ x
_ = foldn _ refl (λ _ → cong suc)    {- Yup, same proof as previous -}

_ : ∀ (x : ℕ) → x ^ 1 ≡ x
_ = foldn _ refl (λ _ → cong suc)    {- No change, same proof as previous -}
\end{code}
Unfortunately, we are manually copy-pasting the same proof /pattern/.
#+begin_quote org
When you see repetition, copy-pasting, know that there is room for improvement! (•̀ᴗ•́)و

Don't repeat yourself!
#+end_quote

Repetition can be mitigated a number of ways, including typeclasses or metaprogramming, for example.
The latter requires possibly less thought and it's the topic of this article, so let's do that :smile:

*Exercise*: Following the template of the previous exercises, fill in the missing parts below.
Hint: It's nearly the same level of difficulty as the previous exercises.
\begin{spec}
make-rid : (let A = ℕ) (_⊕_ : A → A → A) (e : A) → Name → TC ⊤
make-rid _⊕_ e nom
 = do ⋯

_ : ∀{x : ℕ} → x + 0 ≡ x
_ = nice where unquoteDecl nice = make-rid _+_ 0 nice
\end{spec}
:Solution:
\begin{code}
make-rid : (let A = ℕ) (_⊕_ : A → A → A) (e : A) → Name → TC ⊤
make-rid _⊕_ e nom
 = do let η = nom
      let clauses =   clause [ 𝒽𝓇𝒶 (con (quote zero) []) ] (con (quote refl) [])
                    ∷ clause [ 𝒽𝓇𝒶 (con (quote suc)  [ 𝓋𝓇𝒶 (var "n") ]) ]
                             (def (quote cong) (𝓋𝓇𝒶 (quoteTerm suc) ∷ 𝓋𝓇𝒶 (def nom []) ∷ [])) ∷ []
      τ ← quoteTC (∀{x : ℕ} → x ⊕ e ≡ x)
      declareDef (𝓋𝓇𝒶 η) τ
      defineFun η clauses

_ : ∀{x : ℕ} → x + 0 ≡ x
_ = nice where unquoteDecl nice = make-rid _+_ 0 nice
\end{code}
:End:

There's too much syntactic overhead here, let's use macros instead.
\begin{code}
macro
  _trivially-has-rid_ : (let A = ℕ) (_⊕_ : A → A → A) (e : A) → Term → TC ⊤
  _trivially-has-rid_ _⊕_ e goal
   = do τ ← quoteTC (λ(x : ℕ) → x ⊕ e ≡ x)
        unify goal (def (quote foldn)            {- Using foldn    -}
          ( 𝓋𝓇𝒶 τ                                {- Type P         -}
          ∷ 𝓋𝓇𝒶 (con (quote refl) [])            {- Base case      -}
          ∷ 𝓋𝓇𝒶 (λ𝓋 "_" ↦ quoteTerm (cong suc))  {- Inductive step -}
          ∷ []))
\end{code}

Now the proofs have minimal repetition /and/ the proof pattern is written only /once/:
\begin{code}
_ : ∀ (x : ℕ) → x + 0 ≡ x
_ = _+_ trivially-has-rid 0

_ : ∀ (x : ℕ) → x * 1 ≡ x
_ = _*_ trivially-has-rid 1

_ : ∀ (x : ℕ) → x * 1 ≡ x
_ = _^_ trivially-has-rid 1
\end{code}

Note we could look at the type of the goal, find the operator ~_⊕_~ and the unit;
they need not be passed in. Later we will see how to reach into the goal type
and pull pieces of it out for manipulation (•̀ᴗ•́)و

It would have been ideal if we could have defined our macro without using ~foldn~;
I could not figure out how to do that. 😧

Before one abstracts a pattern into a macro, it's useful to have a few instances
of the pattern beforehand. When abstracting, one may want to compare how we think
versus how Agda's thinking. For example, you may have noticed that in the previous
macro, Agda normalised the expression ~suc n + 0~ into ~suc (n + 0)~ by invoking the definition
of ~_+_~. We may inspect the goal of a function with the ~quoteGoal ⋯ in ⋯~ syntax:

\begin{code}
+-rid′ : ∀{n} → n + 0 ≡ n
+-rid′ {zero}  = refl
+-rid′ {suc n} = quoteGoal e in
  let
    suc-n : Term
    suc-n = con (quote suc) [ 𝓋𝓇𝒶 (var 0 []) ]

    lhs : Term
    lhs = def (quote _+_) (𝓋𝓇𝒶 suc-n ∷ 𝓋𝓇𝒶 (lit (nat 0)) ∷ [])

    {- Check our understanding of what the goal is “e”. -}
    _ : e ≡ def (quote _≡_)
                 (𝒽𝓇𝒶 (quoteTerm Level.zero) ∷ 𝒽𝓇𝒶 (quoteTerm ℕ)
                 ∷ 𝓋𝓇𝒶 lhs ∷ 𝓋𝓇𝒶 suc-n ∷ [])
    _ = refl

    {- What does it look normalised. -}
    _ :   quoteTerm (suc (n + 0) ≡ n)
         ≡ unquote λ goal → (do g ← normalise goal; unify g goal)
    _ = refl
  in
  cong suc +-rid′
\end{code}

It would be really nice to simply replace the last line by a macro, say ~induction~.
Unfortunately, for that I would need to obtain the name ~+-rid′~, which as far as I could
tell is not possible with the current reflection mechanism.

* Our First Real Proof Tactic

When we have a proof ~p : x ≡ y~ it is a nuisance to have to write ~sym p~ to prove ~y ≡ x~
─we have to remember which ‘direction’ ~p~. Let's alleviate such a small burden, then use
the tools here to alleviate a larger burden later; namely, rewriting subexpressions.

Given ~p : x ≡ y~, we cannot simply yield ~def (quote sym) [ 𝓋𝓇𝒶 p ]~ since ~sym~ actually
takes four arguments ─compare when we quoted ~_≡_~ earlier. Instead, we infer type of ~p~
to be, say, ~quoteTerm (_≡_ {ℓ} {A} x y)~. Then we can correctly provide all the required arguments.

\begin{code}
≡-type-info : Term → TC (Arg Term × Arg Term × Term × Term)
≡-type-info (def (quote _≡_) (𝓁 ∷ 𝒯 ∷ arg _ l ∷ arg _ r ∷ [])) = returnTC (𝓁 , 𝒯 , l , r)
≡-type-info _ = typeError [ strErr "Term is not a ≡-type." ]
\end{code}

What if later we decided that we did not want a proof of ~x ≡ y~, but rather of ~x ≡ y~.
In this case, the orginal proof ~p~ suffices. Rather than rewriting our proof term, our
macro could try providing it if the symmetry application fails.

\begin{code}
{- Syntactic sugar for trying a computation, if it fails then try the other one -}
try-fun : ∀ {a} {A : Set a} → TC A → TC A → TC A
try-fun = catchTC

syntax try-fun t f = try t or-else f
\end{code}

With the setup in hand, we can now form our macro:
\begin{code}
macro
  apply₁ : Term → Term → TC ⊤
  apply₁ p goal = try (do τ ← inferType p
                          𝓁 , 𝒯 , l , r ← ≡-type-info τ
                          unify goal (def (quote sym) (𝓁 ∷ 𝒯 ∷ 𝒽𝓇𝒶 l ∷ 𝒽𝓇𝒶 r ∷ 𝓋𝓇𝒶 p ∷ [])))
                  or-else
                       unify goal p
\end{code}

For example:
\begin{code}
postulate 𝓍 𝓎 : ℕ
postulate 𝓆 : 𝓍 + 2 ≡ 𝓎

{- Same proof yields two theorems! (งಠ_ಠ)ง -}
_ : 𝓎 ≡ 𝓍 + 2
_ = apply₁ 𝓆

_ : 𝓍 + 2 ≡ 𝓎
_ = apply₁ 𝓆
\end{code}

Let's furnish ourselves with the ability to inspect the /produced/ proofs.
\begin{code}
{- Type annotation -}
syntax has A a = a ∶ A

has : ∀ (A : Set) (a : A) → A
has A a = a
\end{code}
We are using the ‘ghost colon’ obtained with input ~\:~.

Let's try this on an arbitrary type:
\begin{code}
woah : {A : Set} (x y : A) → x ≡ y → (y ≡ x) × (x ≡ y)
woah x y p = apply₁ p , apply₁ p

  where -- Each invocation generates a different proof, indeed:

  first-pf : (apply₁ p ∶ (y ≡ x)) ≡ sym p
  first-pf = refl

  second-pf : (apply₁ p ∶ (x ≡ y)) ≡ p
  second-pf = refl
\end{code}

It is interesting to note that on non ≡-terms, ~apply₁~ is just a no-op.
Why might this be the case?
\begin{code}
_ : ∀ {A : Set} {x : A} → apply₁ x ≡ x
_ = refl

_ : apply₁ "huh" ≡ "huh"
_ = refl
\end{code}

*Exercise:* When we manually form a proof invoking symmetry we simply write, for example, ~sym p~
and the implict arguments are inferred. We can actually do the same thing here! We were a bit dishonest above. 👂
Rewrite ~apply₁~, call it ~apply₂, so that the ~try~ block is a single, unparenthesised, ~unify~ call.
:Solution:
\begin{code}
macro
  apply₂ : Term → Term → TC ⊤
  apply₂ p goal = try unify goal (def (quote sym)  (𝓋𝓇𝒶 p ∷ []))
                  or-else unify goal p

_ : {A : Set} (x y : A) → x ≡ y → (y ≡ x) × (x ≡ y)
_ = λ x y p → apply₂ p , apply₂ p
\end{code}
:End:

*Exercise:* Extend the previous macro so that we can prove statements of the form ~x ≡ x~ regardless of what ~p~
proves. Aesthetics hint: ~try_or-else_~ doesn't need brackets in this case, at all.
\begin{spec}
macro
  apply₃ : Term → Term → TC ⊤
  apply₃ p goal = ⋯

yummah : {A : Set} {x y : A} (p : x ≡ y)  →  x ≡ y  ×  y ≡ x  ×  y ≡ y
yummah p = apply₃ p , apply₃ p , apply₃ p
\end{spec}
:Solution:
\begin{code}
macro
  apply₃ : Term → Term → TC ⊤
  apply₃ p goal = try unify goal (def (quote sym) (𝓋𝓇𝒶 p ∷ []))
                  or-else try unify goal p
                          or-else unify goal (con (quote refl) [])

yummah : {A : Set} {x y : A} (p : x ≡ y)  →  x ≡ y  ×  y ≡ x  ×  y ≡ y
yummah p = apply₃ p , apply₃ p , apply₃ p
\end{code}
:End:

*Exercise:* Write the following seemingly silly macro.
Hint: You cannot use the ~≡-type-info~ method directly, instead you must invoke ~getType~ beforehand.
\begin{spec}
≡-type-info′ : Name → TC (Arg Term × Arg Term × Term × Term)
≡-type-info′ = ⋯

macro
  sumSides : Name → Term → TC ⊤
  sumSides n goal = ⋯

_ : sumSides 𝓆 ≡ 𝓍 + 2 + 𝓎
_ = refl
\end{spec}
:Solution:
\begin{code}
≡-type-info′ : Name → TC (Arg Term × Arg Term × Term × Term)
≡-type-info′ n = do τ ← getType n; ≡-type-info τ

macro
  sumSides : Name → Term → TC ⊤
  sumSides n goal = do _ , _ , l , r ← ≡-type-info′ n; unify goal (def (quote _+_) (𝓋𝓇𝒶 l ∷ 𝓋𝓇𝒶 r ∷ []))

_ : sumSides 𝓆 ≡ 𝓍 + 2 + 𝓎
_ = refl
\end{code}
:End:

*Exercise:* Write two macros, ~left~ and ~right~, such that
~sumSides q  ≡ left q + right q~, where ~q~ is a known name.
These two macros provide the left and right hand sides of the
≡-term they are given.
:Solution:
\begin{code}
macro
  left : Name → Term → TC ⊤
  left n goal = do _ , _ , l , r ← ≡-type-info′ n; unify goal l

  right : Name → Term → TC ⊤
  right n goal = do _ , _ , l , r ← ≡-type-info′ n; unify goal r

_ : sumSides 𝓆  ≡  left 𝓆 + right 𝓆
_ = refl

_ : left 𝓆 ≡ 𝓍 + 2
_ = refl

_ : right 𝓆 ≡ 𝓎
_ = refl
\end{code}
:End:

* Heuristic for Writing a Macro

I have found the following stepwise refinement approach to be useful in constructing
macros. ─Test Driven Development in a proof-centric setting─

1. Write a no-op macro: ~mymacro p goal = unify p goal~.
1. Write the test case ~mymacro p ≡ p~.
2. Feel good, you've succeeded.
3. Alter the test ever so slightly to become closer to your goal.
4. The test now breaks, go fix it.
5. Go to step 3.

For example, suppose we wish to consider proofs ~p~ of expressions of the form ~h x ≡ y~
and our macro is intended to obtain the function ~h~. We proceed as follows:
0. Postulate ~x, y, h, p~ so the problem is well posed.
1. Use the above approach to form a no-op macro.
2. Refine the test to ~mymacro p ≡ λ e → 0~ and refine the macro as well.
3. Refine the test to ~mymacro p ≡ λ e → e~ and refine the macro as well.
4. Eventually succeeded in passing the desired test ~mymacro p ≡ λ e → h e~
    ─then eta reduce.

   Along the way, it may be useful to return the /string/ name of ~h~
   or rewrite the test as ~_≡_ {Level.zero} {ℕ → ℕ} (mymacro p) ≡ ⋯~.
   This may provide insight on how to repair or continue with macro construction.

5. Throw away the postultes, one at a time, making them arguments declared in the test;
    refine macro each time so the test continues to pass as each postulate is removed.
    Each postulate removal may require existing helper functions to be altered.

6. We have considered function applications, then variable funcctions, finally
   consider constructors. Ensure tests cover all these, for this particular problem.

*Exercise:* Carry this through to produce the above discussed example macro, call it ~≡-head~. To help you on your
way, here is a useful function:
\begin{code}
{- If we have “f $ args” return “f”. -}
$-head : Term → Term
$-head (var v args) = var v []
$-head (con c args) = con c []
$-head (def f args) = def f []
$-head (pat-lam cs args) = pat-lam cs []
$-head t = t
\end{code}
:Solution:
\begin{code}

postulate 𝒽 : ℕ → ℕ
postulate 𝒹 𝓮 : ℕ
postulate 𝓅𝒻 : 𝒽 𝒹 ≡ 𝓮
postulate 𝓅𝒻′ : suc 𝒹 ≡ 𝓮

macro
  ≡-head : Term → Term → TC ⊤
  ≡-head p goal = do τ ← inferType p
                     _ , _ , l , _ ← ≡-type-info τ
                     {- Could have used ‘r’ here as well. -}
                     unify goal ($-head l)

_ : quoteTerm (left 𝓅𝒻) ≡ def (quote 𝒽) [ 𝓋𝓇𝒶 (quoteTerm 𝒹) ]
_ = refl

_ : ≡-head 𝓅𝒻 ≡ 𝒽
_ = refl

_ : ≡-head 𝓅𝒻′ ≡ suc
_ = refl

_ : ∀ {g : ℕ → ℕ} {pf″ : g 𝒹 ≡ 𝓮} → ≡-head pf″ ≡ g
_ = refl

_ : ∀ {l r : ℕ} {g : ℕ → ℕ} {pf″ : g l ≡ r} → ≡-head pf″ ≡ g
_ = refl

_ : ∀ {l r s : ℕ} {p : l + r ≡ s} → ≡-head p ≡ _+_
_ = refl
\end{code}
:End:


With the ability to obtain functions being applied in propositional equalities,
we can now turn to lifiting a proof from ~x ≡ y~ to suffice proving ~f x ≡ f y~.
We start with the desired goal and use the stepwise refinement approach outlined
earlier to arrive at:
\begin{code}
macro
  apply₄ : Term → Term → TC ⊤
  apply₄ p goal = try (do τ ← inferType goal
                          _ , _ , l , r ← ≡-type-info τ
                          unify goal ((def (quote cong) (𝓋𝓇𝒶 ($-head l) ∷ 𝓋𝓇𝒶 p ∷ []))))
                  or-else unify goal p

_ : ∀ {x y : ℕ} {f : ℕ → ℕ} (p : x ≡ y)  → f x ≡ f y
_ = λ p → apply₄ p

_ : ∀ {x y : ℕ} {f g : ℕ → ℕ} (p : x ≡ y)
    →  x ≡ y
    -- →  f x ≡ g y {- “apply₄ p” now has a unification error ^_^ -}
_ = λ p → apply₄ p
\end{code}

* What about somewhere deep within a subexpression?

Consider,
\begin{spec}
             suc X + (X * suc X + suc X)
           ≡⟨ cong (λ it → suc X + it) (+-suc _ _) ⟩
             suc X + suc (X * suc X + X)
\end{spec}
Can we find ~(λ it → suc X + it)~ mechanically ;-)

Using the same refinement apporach outlined earlier, we begin with the following
working code then slowly, one piece at a time, replace the whole thing with an
~unquote (unify (quoteTerm ⋯workingCodeHere⋯))~. Then we push the ~quoteTerm~
further in as much as possible and construct the helper functions to make
this transation transpire.
\begin{code}
open import Data.Nat.Properties
{- +-suc : ∀ m n → m + suc n ≡ suc (m + n) -}

test₀ : ∀ {m n k : ℕ} → k + (m + suc n) ≡ k + suc (m + n)
test₀ {m} {n} {k} = cong (k +_) (+-suc m n)
\end{code}

Let's follow the aforementioned approach by starting out with some postulates.
\begin{code}
postulate 𝒳 : ℕ
postulate 𝒢 : suc 𝒳 + (𝒳 * suc 𝒳 + suc 𝒳)  ≡  suc 𝒳 + suc (𝒳 * suc 𝒳 + 𝒳)

𝒮𝒳 : Arg Term
𝒮𝒳 = 𝓋𝓇𝒶 (con (quote suc) [ 𝓋𝓇𝒶 (quoteTerm 𝒳) ])

𝒢ˡ 𝒢ʳ : Term
𝒢ˡ = def (quote _+_) (𝒮𝒳 ∷ 𝓋𝓇𝒶 (def (quote _+_) (𝓋𝓇𝒶 (def (quote _*_) (𝓋𝓇𝒶 (quoteTerm 𝒳) ∷ 𝒮𝒳 ∷ [])) ∷ 𝒮𝒳 ∷ [])) ∷ [])
𝒢ʳ = def (quote _+_) (𝒮𝒳 ∷ 𝓋𝓇𝒶 (con (quote suc) [ 𝓋𝓇𝒶 (def (quote _+_) (𝓋𝓇𝒶 (def (quote _*_) (𝓋𝓇𝒶 (quoteTerm 𝒳) ∷ 𝒮𝒳 ∷ [])) ∷ 𝓋𝓇𝒶 (quoteTerm 𝒳) ∷ [])) ]) ∷ [])
\end{code}

It seems that the left and right sides of 𝒢 “meet” at ~def (quote _+_) (𝒮𝒳 ∷ [])~:
We check the equality of the quoted operator, ~_+_~, then recursively check the arguments.
Whence the following naive algorithm:
\begin{code}
{- Should definitely be in the standard library -}
⌊_⌋ : ∀ {a} {A : Set a} → Dec A → Bool
⌊ yes p ⌋ = true
⌊ no ¬p ⌋ = false

import Agda.Builtin.Reflection as Builtin

_$-≟_ : Term → Term → Bool
con c args $-≟ con c′ args′ = Builtin.primQNameEquality c c′
def f args $-≟ def f′ args′ = Builtin.primQNameEquality f f′
var x args $-≟ var x′ args′ = ⌊ x Nat.≟ x′ ⌋
_ $-≟ _ = false

{- Only gets heads and as much common args, not anywhere deep. :'( -}
infix 5 _⊓_
{-# TERMINATING #-} {- Fix this by adding fuel (con c args) ≔ 1 + length args -}
_⊓_ : Term → Term → Term
l ⊓ r with l $-≟ r | l | r
...| false | x | y = unknown
...| true | var f args | var f′ args′ = var f (List.zipWith (λ{ (arg i!! t) (arg j!! s) → arg i!! (t ⊓ s) }) args args′)
...| true | con f args | con f′ args′ = con f (List.zipWith (λ{ (arg i!! t) (arg j!! s) → arg i!! (t ⊓ s) }) args args′)
...| true | def f args | def f′ args′ = def f (List.zipWith (λ{ (arg i!! t) (arg j!! s) → arg i!! (t ⊓ s) }) args args′)
...| true | ll | _ = ll {- Left biased; using ‘unknown’ does not ensure idempotence. -}
\end{code}

# You would think the ~var~ and ~con~ cases /should/ also be considered, but they're not. Why is that?
#
The bodies have names involving ~!!~, this is to indicate a location of improvement.
Indeed, this naive algorithm ignores visibility and relevance of arguments ─far from ideal.

Joyously this works!  😂
\begin{code}
_ : 𝒢ˡ ⊓ 𝒢ʳ ≡ def (quote _+_) (𝒮𝒳 ∷ 𝓋𝓇𝒶 unknown ∷ [])
_ = refl

{- test using argument function 𝒶 and argument number X -}
_ : {X : ℕ} {𝒶 : ℕ → ℕ}
  →
    let gl = quoteTerm (𝒶 X + (X * 𝒶 X + 𝒶 X))
        gr = quoteTerm (𝒶 X + 𝒶 (X * 𝒶 X + X))
    in gl ⊓ gr ≡ def (quote _+_) (𝓋𝓇𝒶 (var 0 [ 𝓋𝓇𝒶 (var 1 []) ]) ∷ 𝓋𝓇𝒶 unknown ∷ [])
_ = refl
\end{code}
The ~unknown~ terms are far from desirable ─we ought to replace them with sections; i.e., an anonoymous lambda.
My naive algorithm to achieve a section from a term containing ‘unknown’s is as follows:
1. Replace every ~unknown~ with a De Bruijn index.
2. Then, find out how many unknowns there are, and for each, stick an anonoymous lambda at the front.
   + Sticking a lambda at the front breaks existing De Bruijn indices, so increment them for each lambda.

There is clear inefficiency here, but I'm not aiming to be efficient, just believable to some degree.

\begin{code}
{- ‘unknown’ goes to a variable, a De Bruijn index -}
unknown-elim : ℕ → List (Arg Term) → List (Arg Term)
unknown-elim n [] = []
unknown-elim n (arg i unknown ∷ xs) = arg i (var n []) ∷ unknown-elim (n + 1) xs
unknown-elim n (arg i (var x args) ∷ xs) = arg i (var (n + suc x) args) ∷ unknown-elim n xs
unknown-elim n (arg i x ∷ xs)       = arg i x ∷ unknown-elim n xs
{- Essentially we want: body(unknownᵢ)  ⇒  λ _ → body(var 0)
   However, now all “var 0” references in “body” refer to the wrong argument;
   they now refer to “one more lambda away than before”. -}

unknown-count : List (Arg Term) → ℕ
unknown-count [] = 0
unknown-count (arg i unknown ∷ xs) = 1 + unknown-count xs
unknown-count (arg i _ ∷ xs) = unknown-count xs

unknown-λ : ℕ → Term → Term
unknown-λ zero body = body
unknown-λ (suc n) body = unknown-λ n (λ𝓋 "section" ↦ body)

{- Replace ‘unknown’ with sections -}
patch : Term → Term
patch it@(def f args) = unknown-λ (unknown-count args) (def f (unknown-elim 0 args))
patch it@(var f args) = unknown-λ (unknown-count args) (var f (unknown-elim 0 args))
patch it@(con f args) = unknown-λ (unknown-count args) (con f (unknown-elim 0 args))
patch t = t
\end{code}

Putting meet, ~_⊓_~, and this ~patch~ together into a macro:
\begin{code}
macro
  spine : Term → Term → TC ⊤
  spine p goal
    = do τ ← inferType p
         _ , _ , l , r ← ≡-type-info τ
         unify goal (patch (l ⊓ r))
\end{code}

The expected tests pass ─so much joy :joy:
\begin{code}
_ : spine 𝒢 ≡ suc 𝒳 +_
_ = refl

module testing-postulated-functions where
  postulate 𝒶 : ℕ → ℕ
  postulate _𝒷_ : ℕ → ℕ → ℕ
  postulate 𝓰 : 𝒶 𝒳  𝒷  𝒳  ≡  𝒶 𝒳  𝒷  𝒶 𝓍

  _ : spine 𝓰 ≡ (𝒶 𝒳 𝒷_)
  _ = refl

_ : {X : ℕ} {G : suc X + (X * suc X + suc X)  ≡  suc X + suc (X * suc X + X)}
  → quoteTerm G ≡ var 0 []
_ = refl
\end{code}

The tests for ~≡-head~ still go through using ~spine~
which can thus be thought of as a generalisation ;-)
:OlderTests:
\begin{code}
_ : spine 𝓅𝒻 ≡ 𝒽
_ = refl

_ : spine 𝓅𝒻′ ≡ suc
_ = refl

_ : ∀ {g : ℕ → ℕ} {pf″ : g 𝒹 ≡ 𝓮} → spine pf″ ≡ g
_ = refl

_ : ∀ {l r : ℕ} {g : ℕ → ℕ} {pf″ : g l ≡ r} → spine pf″ ≡ g
_ = refl

_ : ∀ {l r s : ℕ} {p : l + r ≡ s} → spine p ≡ _+_
_ = refl
\end{code}
:End:

Now the original problem is dealt with as a macro:
\begin{code}
macro
  apply₅ : Term → Term → TC ⊤
  apply₅ p hole
    = do τ ← inferType hole
         _ , _ , l , r ← ≡-type-info τ
         unify hole ((def (quote cong)
              (𝓋𝓇𝒶 (patch (l ⊓ r)) ∷ 𝓋𝓇𝒶 p ∷ [])))
\end{code}

Curious, why in the following tests we cannot simply use ~+-suc _ _~?
\begin{code}
_ : suc 𝒳 + (𝒳 * suc 𝒳 + suc 𝒳)  ≡  suc 𝒳 + suc (𝒳 * suc 𝒳 + 𝒳)
_ = apply₅ (+-suc (𝒳 * suc 𝒳) 𝒳)

test₁ : ∀ {m n k : ℕ} → k + (m + suc n) ≡ k + suc (m + n)
test₁ {m} {n} {k} = apply₅ (+-suc m n)
\end{code}

This is super neat stuff ^_^

* TODO COMMENT “test” macro

test t ↦   _ : t; _ = refl

Agda has no support for ,@list style &rest args like in lisp :'(

* COMMENT nope, not here yet
Let's use this. Below is an extraction of one of the first assignments for a class
I taught this year ─CompSci 3EA3 Specfications and Correctness. Unfortunately, the
~cong~ and explicit associativity made Agda appear a bit clunky at first; let's change that
impression.
\begin{code}
open import Relation.Binary.PropositionalEquality using () renaming (refl to definition-chasing)
open import Data.Nat.Properties

module PrerequisiteExam where

  open ≡-Reasoning

  lemma : ∀ (X : ℕ) → Σ[ m ∈ ℕ ] (2 * m  ≡  X * X + X)
  lemma zero    = 0 , refl
  lemma (suc X) = m , sym pf
    where
      inductive-hypothesis = lemma X
      m′ = proj₁ inductive-hypothesis
      pf′ = proj₂ inductive-hypothesis

      m = suc X + m′

      pf = begin
             {- We start with the rhs, since it's more complicated. -}
             (suc X) * (suc X) + (suc X)
           ≡⟨ definition-chasing ⟩
             {- Go into the hole blow and enter C-c C-Enter to fill it. -}
             (suc X + X * suc X) + suc X
           ≡⟨ +-assoc (suc X) (X * suc X) (suc X) ⟩
             {- We have to explicitly invoke associativity! -}
             suc X + (X * suc X + suc X)
           ≡⟨ cong (λ it → suc X + it) (+-suc _ _) ⟩
             {- We also have to explicitly invoke congruence,
                similar to using monotonicity in 2DM3. -}
             suc X + suc (X * suc X + X)
           ≡⟨ cong (λ it → suc X + suc (it + X)) (*-comm X (suc X)) ⟩
             suc X + suc (suc X * X + X)
           ≡⟨ definition-chasing ⟩
             {- Definition chasing (reflexivity) steps are optional,
                but we'll often put them in for readability. -}
             suc X + suc (X + X * X + X)
           ≡⟨ cong (λ it → suc X + suc it) (+-assoc X (X * X) X) ⟩
             suc X + suc (X + (X * X + X))
           ≡⟨ cong (λ it → suc X + suc (X + it)) (sym pf′) ⟩
             {- Here we can use the induction hypothesis. -}
             suc X + suc (X + 2 * m′)
           ≡⟨ definition-chasing ⟩
             suc X + (suc X + 2 * m′)
           ≡⟨ sym (+-assoc (suc X) (suc X) (2 * m′)) ⟩
             (suc X + suc X) + 2 * m′
           ≡⟨ cong (λ it → (suc X + it) + 2 * m′) (sym (+-identityʳ _)) ⟩
             (suc X + (suc X + 0)) + 2 * m′
           ≡⟨ definition-chasing ⟩
             2 * suc X + 2 * m′
           ≡⟨ sym (*-distribˡ-+ 2 (suc X) m′) ⟩
             2 * (suc X + m′)
           ≡⟨ definition-chasing ⟩
             {- (suc X + m′) looks like a good candidate for m,
                so we can define m to be it by filling the hole for m above. -}
             2 * m
           ∎
\end{code}

Takes II:
\begin{code}
macro
  apply : Term → Term → TC ⊤
  apply p goal = try (do τ ← inferType goal
                         _ , _ , l , r ← ≡-type-info τ
                         unify goal ((def (quote cong) (𝓋𝓇𝒶 ($-head l) ∷ 𝓋𝓇𝒶 p ∷ []))))
                 or-else try unify goal (def (quote sym) (𝓋𝓇𝒶 p ∷ []))
                         or-else try unify goal p
                                 or-else unify goal (con (quote refl) [])

module ≡-Reasoning-with-tactics {a} {A : Set a} where

  open ≡-Reasoning public hiding (_≡⟨_⟩_)

  -- infixr 2 _≡⟨_⟩_

  -- _≡⟨_⟩_ : ∀ (x {y z} : A) → x ≡ y → y ≡ z → x ≡ z
  -- _ ≡⟨ x≡y ⟩ y≡z = trans (apply x≡y) y≡z

open import Relation.Binary.PropositionalEquality using () renaming (refl to definition-chasing)
open import Data.Nat.Properties

module my/≡-Reasoning where -- {a} {A : Set a} where

  private
    a = Level.zero
    A = ℕ

  infix  3 _∎
  infixr 2 _≡⟨⟩_ _≡⟨_⟩_ _≡˘⟨_⟩_
  infix  1 begin_

  begin_ : ∀{x y : A} → x ≡ y → x ≡ y
  begin_ x≡y = x≡y

  _≡⟨⟩_ : ∀ (x {y} : A) → x ≡ y → x ≡ y
  _ ≡⟨⟩ x≡y = x≡y

  _≡⟨_⟩_ : ∀ (x {y z} : A) → x ≡ y → y ≡ z → x ≡ z
  _ ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

  infixr 2 _≡⟨_⟩′_
  macro
    _≡⟨_⟩′_ : ∀ (x {y} : A) (x≡y : x ≡ y) (y≡z : Term) → Term → TC ⊤
    _≡⟨_⟩′_ xx x≡y y≡z hole
      = do τ ← inferType y≡z
           _ , _ , `y , `z ← ≡-type-info τ
           -- y ← unquoteTC {Level.zero} {ℕ} l
           -- x≈y ← unquoteTC {Level.zero} {xx ≡ y} x≡y
           x≈y ← quoteTC x≡y
           `x  ← quoteTC xx
           unify hole (def (quote trans) (
                   𝒽𝓇𝒶 (quoteTerm Level.zero)
                 ∷ 𝒽𝓇𝒶 (quoteTerm ℕ)
                 ∷ 𝒽𝓇𝒶 `x
                 ∷ 𝒽𝓇𝒶 `y
                 ∷ 𝒽𝓇𝒶 `z
                 ∷
                 𝓋𝓇𝒶 x≈y ∷ 𝓋𝓇𝒶 y≡z ∷ []))
    -- trans x≡y y≡z

  _≡˘⟨_⟩_ : ∀ (x {y z} : A) → y ≡ x → y ≡ z → x ≡ z
  _ ≡˘⟨ y≡x ⟩ y≡z = trans (sym y≡x) y≡z

  _∎ : ∀ (x : A) → x ≡ x
  _∎ _ = refl

module PrerequisiteExam─with─tactics where

  open my/≡-Reasoning -- {Level.zero} {ℕ} -- -with-tactics

  lemma : ∀ (X : ℕ) → Σ[ m ∈ ℕ ] (2 * m  ≡  X * X + X)
  lemma zero    = 0 , refl
  lemma (suc X) = m , sym pf
    where
      inductive-hypothesis = lemma X
      m′ = proj₁ inductive-hypothesis
      pf′ = proj₂ inductive-hypothesis

      m = suc X + m′

      -- neato
      _ : X + (m + suc m′) ≡ X + suc (m + m′)
      _ = apply₅ (+-suc m m′)

      _ : X + (m + suc m′) ≡ X + suc (m + m′)
      _ = begin (
          _≡⟨_⟩_  (X + (m + suc m′))
                  {X + suc (m + m′)} {X + suc (m + m′)} {- items that could not be inferred -}
                  (apply₅ (+-suc m m′))
                  (X + suc (m + m′)∎))

      te : X + (m + suc m′) ≡ X + suc (m + m′)
      -- te =  _≡⟨_⟩′_ (X + (m + suc m′)) (apply₅ (+-suc m m′)) (refl {x = X + suc (m + m′)})
      te = _≡⟨_⟩′_ (X + (m + suc m′)) {y = X + suc (m + m′)} (apply₅ (+-suc m m′)) (refl {x = X + suc (m + m′)})
      -- begin X + (m + suc m′) ≡⟨ apply₅ (+-suc m m′) ⟩′ (X + suc (m + m′) ∎)
      -- apply₅ (+-suc m m′)

      {-
      _ : (suc X + X * suc X) + suc X  ≡  suc X + suc (X * suc X + X)
      _ = begin
             (suc X + X * suc X) + suc X
           ≡⟨ +-assoc (suc X) (X * suc X) (suc X) ⟩
             suc X + (X * suc X + suc X)
           ≡⟨ it ⟩ -- apply₅ (+-suc (X * suc X) X) ⟩
             suc X + suc (X * suc X + X)
           ∎
           where it :  suc (X + (X * suc X + suc X)) ≡ suc (X + suc (X * suc X + X))
                 it = apply₅ (+-suc {!!} {!!})
      -}

      pf : (suc X + X * suc X) + suc X  ≡  2 * m
      pf = begin
             (suc X + X * suc X) + suc X
           ≡⟨ +-assoc (suc X) (X * suc X) (suc X) ⟩
             suc X + (X * suc X + suc X)
           ≡⟨ cong (λ it → suc X + it) (+-suc _ _) ⟩ -- apply₅ (+-suc (X * suc X) X) ⟩ -- cong (λ it → suc X + it) (+-suc _ _) ⟩
             suc X + suc (X * suc X + X)
           ≡⟨ cong (λ it → suc X + suc (it + X)) (*-comm X (suc X)) ⟩
             suc X + suc (X + X * X + X)
           ≡⟨ cong (λ it → suc X + suc it) (+-assoc X (X * X) X) ⟩
             suc X + suc (X + (X * X + X))
           ≡⟨ cong (λ it → suc X + suc (X + it)) (sym pf′) ⟩
             suc X + (suc X + 2 * m′)
           ≡⟨ apply (+-assoc (suc X) (suc X) (2 * m′)) ⟩ -- no sym ♥‿♥
             (suc X + suc X) + 2 * m′
           ≡⟨ cong (λ it → (suc X + it) + 2 * m′) (sym (+-identityʳ _)) ⟩
             (suc X + (suc X + 0)) + 2 * m′
           ≡⟨ definition-chasing ⟩
             2 * suc X + 2 * m′
           ≡⟨ apply (*-distribˡ-+ 2 (suc X) m′) ⟩  -- no sym ♥‿♥
             2 * (suc X + m′)
           ≡⟨ definition-chasing ⟩
             2 * m
           ∎
\end{code}

* COMMENT Flatenning ─& mixins ─anaphoric macros in Agda?

\begin{code}

data Empty : Set₁ where

record Type : Set₁ where
  field Carrier : Set

-- record Magma : Set₁ where
--
-- Magma ≔ Empty ⟫ Type ⟫ (Carrier → Carrier → Carrier)

{- Specfication

   field′ name ∶ type
≅  record Anon : TypeOf(type) where field name : type
≅  name : TypeOf(type)
   name = type

   τ ⟫ τ′
≅  anon : Set $ Typeof(τ) ⊔ Typeof (τ′)
   anon = Σ t : τ • τ′

-}

macro
  _⟫_ : Term → Term → Term → TC ⊤
  _⟫_ τ ρ goal = do unify goal
                      (def (quote Σ) (𝓋𝓇𝒶 τ ∷ 𝓋𝓇𝒶 ρ ∷ []))

testf : Set
testf = Char ⟫ λ (x : Char) → ℕ

el : testf
el = 'c' , 0

--------------------------------------------------------

record Two : Set where
  field
   a : ℕ
   b : ℕ

-- get first field from a record
fields : Definition → TC Name
fields (record′ c (arg _ f ∷ fs)) = returnTC f
fields _ = typeError [ strErr "Nope: No fields" ]

macro
  field₁ : Name → Term → TC ⊤
  field₁ n goal = do τ ← getDefinition n; f ← fields τ; unify goal (def f [])

two₂ : Two → ℕ
two₂ = field₁ Two

-- :smile: yay (งಠ_ಠ)ง

-- it would be nice to generate the names fieldᵢ rather than write them out by hand.

\end{code}

* TODO COMMENT ideas

+ deriving decidable equality

\begin{spec}
data RGB : Set where
  Red Green Blue : RGB

_≟_ : (p q : RGB) → Dec (p ≡ q)

Red ≟ Red = yes refl
Red ≟ Green = no (λ ())
Red ≟ Blue = no (λ ())

Green ≟ Red = no (λ ())
Green ≟ Green = yes refl
Green ≟ Blue = no (λ ())

Blue ≟ Red = no (λ ())
Blue ≟ Green = no (λ ())
Blue ≟ Blue = yes refl
\end{spec}

+ theory combinators

\begin{code}
macro
    plus-to-times : Term → Term → TC ⊤
    plus-to-times (def (quote _+_) (a ∷ b ∷ [])) hole = unify hole (def (quote _*_) (a ∷ b ∷ []))
    plus-to-times v hole = unify hole v

thm : (a b : ℕ) → plus-to-times (a + b) ≡ a * b
thm a b = refl

--------------------------------------------------------
\end{code}


+ flatten: Take a nested record hierarchy and produce a flattened telescope, since
  records cannot be unquoted.

+ 2^50 * 3^313 ≡  3^313 * 2^50 is true by symmetry of *,
  but may timeout if we try to prove things by refl.

* COMMENT README

C-c C-c: evalute src block

#+NAME: make-readme
#+BEGIN_SRC emacs-lisp :results none
(with-temp-buffer
    (insert
    "#+EXPORT_FILE_NAME: README.md
     # HTML: <h1> gentle-intro-to-reflection </h1>

     A slow-paced introduction to reflection in Agda. ---Tactics!

     # The following can also be read as a [[https://alhassy.github.io/literate/][blog post]].

     # TOC: headlines 2
     #+INCLUDE: gentle-intro-to-reflection.lagda
    ")
    (org-mode)
    (org-md-export-to-markdown)
)
#+END_SRC

* COMMENT footer

The org-agda-mode and literate.el come from:
https://github.com/alhassy/org-agda-mode

# Having the make-readme progn below with the local variables causes trees
# to remain folded when moving to agda2-mode.

# Local Variables:
# eval: (setq org-src-preserve-indentation 't)
# eval: (visual-line-mode t)
# eval: (load-file "~/org-agda-mode/org-agda-mode.el")
# eval: (load-file "~/org-agda-mode/literate.el")
# compile-command: (progn (org-babel-tangle) (org-babel-goto-named-src-block "make-readme") (org-babel-execute-src-block) (outline-hide-sublevels 1))
# End:
