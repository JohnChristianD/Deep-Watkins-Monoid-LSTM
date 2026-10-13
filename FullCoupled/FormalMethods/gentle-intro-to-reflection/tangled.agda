{-# OPTIONS
  --lossy-unification
  --backtracking-instance-search
  --experimental-lazy-instances
  --confluence-check
  --polarity
  --auto-inline
  --guarded
  --exact-split
  --no-infer-absurd-clauses
  --keep-covering-clauses
  --no-projection-like
  --erasure
#-}


module tangled where

-- Merged external import surface; internal FullCoupled imports remain module-local.
open import Haskell.Prelude hiding (String; ⊥)
open import MLTT.Spartan hiding (J)
open import Naturals
open import Naturals.Exponentiation
open import Naturals.Division
open import Naturals.Properties
open import Notation.Order
open import Order
open import Rationals.Addition
open import Rationals.Multiplication
open import Rationals.Negation
open import Rationals.Order
open import Rationals.Type
open import UF.Base
open import UF.FunExt
open import UF.PropTrunc
open import UF.Size
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.UA-FunExt

open import Agda.Builtin.Reflection as Builtin



{- [[file:~/reflection/gentle-intro-to-reflection.lagda::*Introduction][Introduction:1]] -}
data RGB : Set where
  Red Green Blue : RGB
{- Introduction:1 ends here -}

{- [[file:~/reflection/gentle-intro-to-reflection.lagda::*~NAME~%20%E2%94%80Type%20of%20known%20identifiers][~NAME~ ─Type of known identifiers:1]] -}
a-name : Name
a-name = quote Nat

isNat : Name → Bool
isNat (quote ℕ) = true
isNat _         = false

-- bad : Set → Name
-- bad s = quote s  {- s is not known -}
{- ~NAME~ ─Type of known identifiers:1 ends here -}

{- [[file:~/reflection/gentle-intro-to-reflection.lagda::*~NAME~%20%E2%94%80Type%20of%20known%20identifiers][~NAME~ ─Type of known identifiers:2]] -}
_ : showName (quote _≡_) ≡ "Agda.Builtin.Equality._≡_"
_ = refl
{- ~NAME~ ─Type of known identifiers:2 ends here -}

{- [[file:~/reflection/gentle-intro-to-reflection.lagda::*~NAME~%20%E2%94%80Type%20of%20known%20identifiers][~NAME~ ─Type of known identifiers:4]] -}
{- Like “$” but for strings. -}
_⟨𝒮⟩_ : (List Char → List Char) → String → String
f ⟨𝒮⟩ s = fromList (f (toList s))

{- This should be in the standard library; I could not locate it. -}
toDec : ∀ {ℓ} {A : Set ℓ} → (p : A → Bool) → Dec (λ a → p a ≡ true)
toDec p x with p x
toDec p x | false = no λ ()
toDec p x | true = yes refl
{- ~NAME~ ─Type of known identifiers:4 ends here -}

{- [[file:~/reflection/gentle-intro-to-reflection.lagda::*~NAME~%20%E2%94%80Type%20of%20known%20identifiers][~NAME~ ─Type of known identifiers:5]] -}
module-name : String
module-name = takeWhile (toDec (λ c → not (c Char.== '.'))) ⟨𝒮⟩ showName (quote Red)
{- ~NAME~ ─Type of known identifiers:5 ends here -}

{- [[file:~/reflection/gentle-intro-to-reflection.lagda::*~NAME~%20%E2%94%80Type%20of%20known%20identifiers][~NAME~ ─Type of known identifiers:7]] -}
strName : Name → String
strName n = drop (1 + String.length module-name) ⟨𝒮⟩ showName n
{- The “1 +” is for the “.” seperator in qualified names. -}

_ : strName (quote Red) ≡ "RGB.Red"
_ = refl
{- ~NAME~ ─Type of known identifiers:7 ends here -}

{- [[file:~/reflection/gentle-intro-to-reflection.lagda::*~Arg~%20%E2%94%80Type%20of%20arguments][~Arg~ ─Type of arguments:1]] -}
{- 𝓋isible 𝓇elevant 𝒶rgument -}
𝓋𝓇𝒶 : {A : Set} → A → Arg A
𝓋𝓇𝒶 = arg (arg-info visible relevant)

{- 𝒽idden 𝓇elevant 𝒶rgument -}
𝒽𝓇𝒶 : {A : Set} → A → Arg A
𝒽𝓇𝒶 = arg (arg-info hidden relevant)
{- ~Arg~ ─Type of arguments:1 ends here -}

{- [[file:~/reflection/gentle-intro-to-reflection.lagda::*~Arg~%20%E2%94%80Type%20of%20arguments][~Arg~ ─Type of arguments:2]] -}
{- 𝓋isible 𝓇elevant 𝓋ariable -}
𝓋𝓇𝓋 : (debruijn : ℕ) (args : List (Arg Term)) → Arg Term
𝓋𝓇𝓋 n args = arg (arg-info visible relevant) (var n args)

{- 𝒽idden 𝓇elevant 𝓋ariable -}
𝒽𝓇𝓋 : (debruijn : ℕ) (args : List (Arg Term)) → Arg Term
𝒽𝓇𝓋 n args = arg (arg-info hidden relevant) (var n args)
{- ~Arg~ ─Type of arguments:2 ends here -}

{- [[file:~/reflection/gentle-intro-to-reflection.lagda::*Example:%20Simple%20Types][Example: Simple Types:1]] -}

_ : quoteTerm ℕ ≡ def (quote ℕ) []
_ = refl

_ : quoteTerm List ≡ def (quote List) []
_ = refl

_ : quoteTerm (List ℕ) ≡ def (quote List) (𝓋𝓇𝒶 (quoteTerm ℕ) ∷ [])
_ = refl
{- Example: Simple Types:1 ends here -}

{- [[file:~/reflection/gentle-intro-to-reflection.lagda::*Example:%20Simple%20Terms][Example: Simple Terms:1]] -}
_ : quoteTerm 1 ≡ lit (nat 1)
_ = refl

_ :    quoteTerm (suc zero)
     ≡ con (quote suc) (arg (arg-info visible relevant) (quoteTerm zero) ∷ [])
_ = refl

{- Using our helper 𝓋𝓇𝒶 -}
_ : quoteTerm (suc zero) ≡ con (quote suc) (𝓋𝓇𝒶 (quoteTerm zero) ∷ [])
_ = refl
{- Example: Simple Terms:1 ends here -}

{- [[file:~/reflection/gentle-intro-to-reflection.lagda::*Example:%20Simple%20Terms][Example: Simple Terms:2]] -}
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
{- Example: Simple Terms:2 ends here -}

{- [[file:~/reflection/gentle-intro-to-reflection.lagda::*Example:%20Simple%20Terms][Example: Simple Terms:3]] -}
_ : ∀ {level : Level.Level}{Type : Set level} (x y : Type)
    →   quoteTerm (x ≡ y)
       ≡ def (quote _≡_)
           (𝒽𝓇𝓋 3 [] ∷ 𝒽𝓇𝓋 2 [] ∷ 𝓋𝓇𝓋 1 [] ∷ 𝓋𝓇𝓋 0 [] ∷ [])

_ = λ x y → refl
{- Example: Simple Terms:3 ends here -}

{- [[file:~/reflection/gentle-intro-to-reflection.lagda::*A%20relationship%20between%20~quote~%20and%20~quoteTerm~][A relationship between ~quote~ and ~quoteTerm~:1]] -}
postulate 𝒜 ℬ : Set
postulate 𝒻 : 𝒜 → ℬ
_ : quoteTerm 𝒻 ≡ def (quote 𝒻) []
_ = refl
{- A relationship between ~quote~ and ~quoteTerm~:1 ends here -}

{- [[file:~/reflection/gentle-intro-to-reflection.lagda::*A%20relationship%20between%20~quote~%20and%20~quoteTerm~][A relationship between ~quote~ and ~quoteTerm~:2]] -}
module _ {A B : Set} {f : A → B} where
  _ : quoteTerm f ≡ var 0 []
  _ = refl
{- A relationship between ~quote~ and ~quoteTerm~:2 ends here -}

{- [[file:~/reflection/gentle-intro-to-reflection.lagda::*Example:%20Lambda%20Terms][Example: Lambda Terms:1]] -}
_ : quoteTerm ((λ x → x) "nice") ≡ lit (string "nice")
_ = refl
{- Example: Lambda Terms:1 ends here -}

{- [[file:~/reflection/gentle-intro-to-reflection.lagda::*Example:%20Lambda%20Terms][Example: Lambda Terms:2]] -}
id : {A : Set} → A → A
id x = x

_ :   quoteTerm (λ (x : ℕ) → id x)
    ≡ def (quote id) (𝒽𝓇𝒶 (def (quote ℕ) []) ∷ [])
_ = refl
{- Example: Lambda Terms:2 ends here -}

{- [[file:~/reflection/gentle-intro-to-reflection.lagda::*Example:%20Lambda%20Terms][Example: Lambda Terms:3]] -}
_ :   quoteTerm (id "a")
    ≡ def (quote id)
        (𝒽𝓇𝒶 (def (quote String) []) ∷  𝓋𝓇𝒶 (lit (string "a")) ∷ [])
_ = refl
{- Example: Lambda Terms:3 ends here -}

{- [[file:~/reflection/gentle-intro-to-reflection.lagda::*Example:%20Lambda%20Terms][Example: Lambda Terms:4]] -}
_ : quoteTerm (λ (x : Bool) → x) ≡ lam visible (abs "x" (var 0 []))
_ = refl
{- Example: Lambda Terms:4 ends here -}

{- [[file:~/reflection/gentle-intro-to-reflection.lagda::*Example:%20Lambda%20Terms][Example: Lambda Terms:5]] -}
_ : quoteTerm (λ (a : ℕ) (f : ℕ → ℕ) → f a)
    ≡  lam visible (abs "a"
         (lam visible (abs "f"
           (var 0 (arg (arg-info visible relevant) (var 1 []) ∷ [])))))
_ = refl
{- Example: Lambda Terms:5 ends here -}

{- [[file:~/reflection/gentle-intro-to-reflection.lagda::*Example:%20Lambda%20Terms][Example: Lambda Terms:6]] -}
infixr 5 λ𝓋_↦_  λ𝒽_↦_

λ𝓋_↦_  λ𝒽_↦_ : String → Term → Term
λ𝓋 x ↦ body  = lam visible (abs x body)
λ𝒽 x ↦ body  = lam hidden (abs x body)
{- Example: Lambda Terms:6 ends here -}

{- [[file:~/reflection/gentle-intro-to-reflection.lagda::*Example:%20Lambda%20Terms][Example: Lambda Terms:7]] -}
_ :   quoteTerm (λ (a : ℕ) (f : ℕ → ℕ) → f a)
    ≡ λ𝓋 "a" ↦ λ𝓋 "f" ↦ var 0 [ 𝓋𝓇𝒶 (var 1 []) ]
_ = refl
{- Example: Lambda Terms:7 ends here -}

{- [[file:~/reflection/gentle-intro-to-reflection.lagda::*Example:%20Lambda%20Terms][Example: Lambda Terms:8]] -}
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
{- Example: Lambda Terms:8 ends here -}

{- [[file:~/reflection/gentle-intro-to-reflection.lagda::*Example:%20Lambda%20Terms][Example: Lambda Terms:9]] -}
_ :   quoteTerm (_≡ "b")
    ≡ λ𝓋 "section" ↦
       (def (quote _≡_)
        (𝒽𝓇𝒶 (def (quote Level.zero) []) ∷
         𝒽𝓇𝒶(def (quote String) []) ∷
         𝓋𝓇𝒶 (var 0 []) ∷
         𝓋𝓇𝒶 (lit (string "b")) ∷ []))
_ = refl
{- Example: Lambda Terms:9 ends here -}

{- [[file:~/reflection/gentle-intro-to-reflection.lagda::*Metaprogramming%20with%20The%20Typechecking%20Monad%20~TC~][Metaprogramming with The Typechecking Monad ~TC~:1]] -}
_>>=_        : ∀ {a b} {A : Set a} {B : Set b} → TC A → (A → TC B) → TC B
_>>=_ = bindTC

_>>_        : ∀ {a b} {A : Set a} {B : Set b} → TC A → TC B → TC B
_>>_  = λ p q → p >>= (λ _ → q)
{- Metaprogramming with The Typechecking Monad ~TC~:1 ends here -}

{- [[file:~/reflection/gentle-intro-to-reflection.lagda::*Unquoting%20%E2%94%80Making%20new%20functions%20&%20types][Unquoting ─Making new functions & types:1]] -}
“ℓ₀” : Arg Term
“ℓ₀” = 𝒽𝓇𝒶 (def (quote Level.zero) [])

“RGB” : Arg Term
“RGB” = 𝒽𝓇𝒶 (def (quote RGB) [])

“Red” : Arg Term
“Red” = 𝓋𝓇𝒶 (con (quote Red) [])
{- Unquoting ─Making new functions & types:1 ends here -}

{- [[file:~/reflection/gentle-intro-to-reflection.lagda::*Unquoting%20%E2%94%80Making%20new%20functions%20&%20types][Unquoting ─Making new functions & types:2]] -}
unquoteDecl IsRed =
  do ty ← quoteTC (RGB → Set)
     declareDef (𝓋𝓇𝒶 IsRed) ty
     defineFun IsRed   [ clause [ 𝓋𝓇𝒶 (var "x") ] (def (quote _≡_) (“ℓ₀” ∷ “RGB” ∷ “Red” ∷ 𝓋𝓇𝓋 0 [] ∷ [])) ]
{- Unquoting ─Making new functions & types:2 ends here -}

{- [[file:~/reflection/gentle-intro-to-reflection.lagda::*Unquoting%20%E2%94%80Making%20new%20functions%20&%20types][Unquoting ─Making new functions & types:3]] -}
red-is-a-solution : IsRed Red
red-is-a-solution = refl

green-is-not-a-solution : ¬ (IsRed Green)
green-is-not-a-solution = λ ()

red-is-the-only-solution : ∀ {c} → IsRed c → c ≡ Red
red-is-the-only-solution refl = refl
{- Unquoting ─Making new functions & types:3 ends here -}

{- [[file:~/reflection/gentle-intro-to-reflection.lagda::*Unquoting%20%E2%94%80Making%20new%20functions%20&%20types][Unquoting ─Making new functions & types:4]] -}
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
{- Unquoting ─Making new functions & types:4 ends here -}

{- [[file:~/reflection/gentle-intro-to-reflection.lagda::*Unquoting%20%E2%94%80Making%20new%20functions%20&%20types][Unquoting ─Making new functions & types:5]] -}
unquoteDecl IsBlue  = declare-Is IsBlue  (quote Blue)
unquoteDecl IsGreen = declare-Is IsGreen (quote Green)

{- Example use -}
disjoint-rgb  : ∀{c} → ¬ (IsBlue c × IsGreen c)
disjoint-rgb (refl , ())
{- Unquoting ─Making new functions & types:5 ends here -}

{- [[file:~/reflection/gentle-intro-to-reflection.lagda::*Unquoting%20%E2%94%80Making%20new%20functions%20&%20types][Unquoting ─Making new functions & types:6]] -}
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
{- Unquoting ─Making new functions & types:6 ends here -}

{- [[file:~/reflection/gentle-intro-to-reflection.lagda::*Unquoting%20%E2%94%80Making%20new%20functions%20&%20types][Unquoting ─Making new functions & types:7]] -}
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
{- Unquoting ─Making new functions & types:7 ends here -}

{- [[file:~/reflection/gentle-intro-to-reflection.lagda::*Sidequest:%20Avoid%20tedious%20~refl~%20proofs][Sidequest: Avoid tedious ~refl~ proofs:1]] -}
just-Red : RGB → RGB
just-Red Red   = Red
just-Red Green = Red
just-Red Blue  = Red

only-Blue : RGB → RGB
only-Blue Blue = Blue
only-Blue _   = Blue
{- Sidequest: Avoid tedious ~refl~ proofs:1 ends here -}

{- [[file:~/reflection/gentle-intro-to-reflection.lagda::*Sidequest:%20Avoid%20tedious%20~refl~%20proofs][Sidequest: Avoid tedious ~refl~ proofs:2]] -}
just-Red-is-constant : ∀{c} → just-Red c ≡ Red
just-Red-is-constant {Red}   = refl
just-Red-is-constant {Green} = refl
just-Red-is-constant {Blue}  = refl

{- Yuck, another tedious proof -}
only-Blue-is-constant : ∀{c} → only-Blue c ≡ Blue
only-Blue-is-constant {Blue}  = refl
only-Blue-is-constant {Red}   = refl
only-Blue-is-constant {Green} = refl
{- Sidequest: Avoid tedious ~refl~ proofs:2 ends here -}

{- [[file:~/reflection/gentle-intro-to-reflection.lagda::*Sidequest:%20Avoid%20tedious%20~refl~%20proofs][Sidequest: Avoid tedious ~refl~ proofs:3]] -}
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
{- Sidequest: Avoid tedious ~refl~ proofs:3 ends here -}

{- [[file:~/reflection/gentle-intro-to-reflection.lagda::*Sidequest:%20Avoid%20tedious%20~refl~%20proofs][Sidequest: Avoid tedious ~refl~ proofs:4]] -}
_ : ∀{c} → just-Red c ≡ Red
_ = nice
  where unquoteDecl nice = by-refls nice (quoteTerm (∀{c} → just-Red c ≡ Red))
{- Sidequest: Avoid tedious ~refl~ proofs:4 ends here -}

{- [[file:~/reflection/gentle-intro-to-reflection.lagda::*Sidequest:%20Avoid%20tedious%20~refl~%20proofs][Sidequest: Avoid tedious ~refl~ proofs:5]] -}
_ : ∀{c} → only-Blue c ≡ Blue
_ = nice
  where unquoteDecl nice = by-refls nice (quoteTerm ∀{c} → only-Blue c ≡ Blue)
{- Sidequest: Avoid tedious ~refl~ proofs:5 ends here -}

{- [[file:~/reflection/gentle-intro-to-reflection.lagda::*C-style%20macros][C-style macros:1]] -}
luckyNum₀ : Term → TC ⊤
luckyNum₀ h = unify h (quoteTerm 55)

num₀ : ℕ
num₀ = unquote luckyNum₀
{- C-style macros:1 ends here -}

{- [[file:~/reflection/gentle-intro-to-reflection.lagda::*C-style%20macros][C-style macros:2]] -}
macro
  luckyNum : Term → TC ⊤
  luckyNum h = unify h (quoteTerm 55)

num : ℕ
num = luckyNum
{- C-style macros:2 ends here -}

{- [[file:~/reflection/gentle-intro-to-reflection.lagda::*C-style%20macros][C-style macros:3]] -}
{- exercise -}
macro
  first : Term → TC ⊤
  first goal = unify goal (var 1 [])

myconst : {A B : Set} → A → B → A
myconst = λ x → λ y → first

mysum : ( {x} y : ℕ) → ℕ
mysum y = y + first
{- end -}
{- C-style macros:3 ends here -}

{- [[file:~/reflection/gentle-intro-to-reflection.lagda::*C-style%20macros][C-style macros:4]] -}
macro
  use : Term → Term → TC ⊤
  use (def _ []) goal = unify goal (quoteTerm "Nice")
  use v goal = unify goal  (quoteTerm "WoahThere")
{- C-style macros:4 ends here -}

{- [[file:~/reflection/gentle-intro-to-reflection.lagda::*C-style%20macros][C-style macros:5]] -}
{- Fully defined, no arguments. -}

2+2≈4 : 2 + 2 ≡ 4
2+2≈4 = refl

_ : use 2+2≈4 ≡ "Nice"
_ = refl

{- ‘p’ has arguments. -}

_ : {x y : ℕ} {p : x ≡ y} → use p ≡ "WoahThere"
_ = refl
{- C-style macros:5 ends here -}

{- [[file:~/reflection/gentle-intro-to-reflection.lagda::*Tedious%20Repetitive%20Proofs%20No%20More!][Tedious Repetitive Proofs No More!:1]] -}
+-rid : ∀{n} → n + 0 ≡ n
+-rid {zero}  = refl
+-rid {suc n} = cong suc +-rid

*-rid : ∀{n} → n * 1 ≡ n
*-rid {zero}  = refl
*-rid {suc n} = cong suc *-rid

^-rid : ∀{n} → n ^ 1 ≡ n
^-rid {zero}  = refl
^-rid {suc n} = cong suc ^-rid
{- Tedious Repetitive Proofs No More!:1 ends here -}

{- [[file:~/reflection/gentle-intro-to-reflection.lagda::*Tedious%20Repetitive%20Proofs%20No%20More!][Tedious Repetitive Proofs No More!:2]] -}
{- “for loops” or “Induction for ℕ” -}
foldn : (P : ℕ → Set) (base : P zero) (ind : ∀ n → P n → P (suc n))
      → ∀(n : ℕ) → P n
foldn P base ind zero    = base
foldn P base ind (suc n) = ind n (foldn P base ind n)
{- Tedious Repetitive Proofs No More!:2 ends here -}

{- [[file:~/reflection/gentle-intro-to-reflection.lagda::*Tedious%20Repetitive%20Proofs%20No%20More!][Tedious Repetitive Proofs No More!:3]] -}
_ : ∀ (x : ℕ) → x + 0 ≡ x
_ = foldn _ refl (λ _ → cong suc)    {- This and next two are the same -}

_ : ∀ (x : ℕ) → x * 1 ≡ x
_ = foldn _ refl (λ _ → cong suc)    {- Yup, same proof as previous -}

_ : ∀ (x : ℕ) → x ^ 1 ≡ x
_ = foldn _ refl (λ _ → cong suc)    {- No change, same proof as previous -}
{- Tedious Repetitive Proofs No More!:3 ends here -}

{- [[file:~/reflection/gentle-intro-to-reflection.lagda::*Tedious%20Repetitive%20Proofs%20No%20More!][Tedious Repetitive Proofs No More!:4]] -}
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
{- Tedious Repetitive Proofs No More!:4 ends here -}

{- [[file:~/reflection/gentle-intro-to-reflection.lagda::*Tedious%20Repetitive%20Proofs%20No%20More!][Tedious Repetitive Proofs No More!:5]] -}
macro
  _trivially-has-rid_ : (let A = ℕ) (_⊕_ : A → A → A) (e : A) → Term → TC ⊤
  _trivially-has-rid_ _⊕_ e goal
   = do τ ← quoteTC (λ(x : ℕ) → x ⊕ e ≡ x)
        unify goal (def (quote foldn)            {- Using foldn    -}
          ( 𝓋𝓇𝒶 τ                                {- Type P         -}
          ∷ 𝓋𝓇𝒶 (con (quote refl) [])            {- Base case      -}
          ∷ 𝓋𝓇𝒶 (λ𝓋 "_" ↦ quoteTerm (cong suc))  {- Inductive step -}
          ∷ []))
{- Tedious Repetitive Proofs No More!:5 ends here -}

{- [[file:~/reflection/gentle-intro-to-reflection.lagda::*Tedious%20Repetitive%20Proofs%20No%20More!][Tedious Repetitive Proofs No More!:6]] -}
_ : ∀ (x : ℕ) → x + 0 ≡ x
_ = _+_ trivially-has-rid 0

_ : ∀ (x : ℕ) → x * 1 ≡ x
_ = _*_ trivially-has-rid 1

_ : ∀ (x : ℕ) → x * 1 ≡ x
_ = _^_ trivially-has-rid 1
{- Tedious Repetitive Proofs No More!:6 ends here -}

{- [[file:~/reflection/gentle-intro-to-reflection.lagda::*Tedious%20Repetitive%20Proofs%20No%20More!][Tedious Repetitive Proofs No More!:7]] -}
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
{- Tedious Repetitive Proofs No More!:7 ends here -}

{- [[file:~/reflection/gentle-intro-to-reflection.lagda::*Our%20First%20Real%20Proof%20Tactic][Our First Real Proof Tactic:1]] -}
≡-type-info : Term → TC (Arg Term × Arg Term × Term × Term)
≡-type-info (def (quote _≡_) (𝓁 ∷ 𝒯 ∷ arg _ l ∷ arg _ r ∷ [])) = returnTC (𝓁 , 𝒯 , l , r)
≡-type-info _ = typeError [ strErr "Term is not a ≡-type." ]
{- Our First Real Proof Tactic:1 ends here -}

{- [[file:~/reflection/gentle-intro-to-reflection.lagda::*Our%20First%20Real%20Proof%20Tactic][Our First Real Proof Tactic:2]] -}
{- Syntactic sugar for trying a computation, if it fails then try the other one -}
try-fun : ∀ {a} {A : Set a} → TC A → TC A → TC A
try-fun = catchTC

syntax try-fun t f = try t or-else f
{- Our First Real Proof Tactic:2 ends here -}

{- [[file:~/reflection/gentle-intro-to-reflection.lagda::*Our%20First%20Real%20Proof%20Tactic][Our First Real Proof Tactic:3]] -}
macro
  apply₁ : Term → Term → TC ⊤
  apply₁ p goal = try (do τ ← inferType p
                          𝓁 , 𝒯 , l , r ← ≡-type-info τ
                          unify goal (def (quote sym) (𝓁 ∷ 𝒯 ∷ 𝒽𝓇𝒶 l ∷ 𝒽𝓇𝒶 r ∷ 𝓋𝓇𝒶 p ∷ [])))
                  or-else
                       unify goal p
{- Our First Real Proof Tactic:3 ends here -}

{- [[file:~/reflection/gentle-intro-to-reflection.lagda::*Our%20First%20Real%20Proof%20Tactic][Our First Real Proof Tactic:4]] -}
postulate 𝓍 𝓎 : ℕ
postulate 𝓆 : 𝓍 + 2 ≡ 𝓎

{- Same proof yields two theorems! (งಠ_ಠ)ง -}
_ : 𝓎 ≡ 𝓍 + 2
_ = apply₁ 𝓆

_ : 𝓍 + 2 ≡ 𝓎
_ = apply₁ 𝓆
{- Our First Real Proof Tactic:4 ends here -}

{- [[file:~/reflection/gentle-intro-to-reflection.lagda::*Our%20First%20Real%20Proof%20Tactic][Our First Real Proof Tactic:5]] -}
{- Type annotation -}
syntax has A a = a ∶ A

has : ∀ (A : Set) (a : A) → A
has A a = a
{- Our First Real Proof Tactic:5 ends here -}

{- [[file:~/reflection/gentle-intro-to-reflection.lagda::*Our%20First%20Real%20Proof%20Tactic][Our First Real Proof Tactic:6]] -}
woah : {A : Set} (x y : A) → x ≡ y → (y ≡ x) × (x ≡ y)
woah x y p = apply₁ p , apply₁ p

  where -- Each invocation generates a different proof, indeed:

  first-pf : (apply₁ p ∶ (y ≡ x)) ≡ sym p
  first-pf = refl

  second-pf : (apply₁ p ∶ (x ≡ y)) ≡ p
  second-pf = refl
{- Our First Real Proof Tactic:6 ends here -}

{- [[file:~/reflection/gentle-intro-to-reflection.lagda::*Our%20First%20Real%20Proof%20Tactic][Our First Real Proof Tactic:7]] -}
_ : ∀ {A : Set} {x : A} → apply₁ x ≡ x
_ = refl

_ : apply₁ "huh" ≡ "huh"
_ = refl
{- Our First Real Proof Tactic:7 ends here -}

{- [[file:~/reflection/gentle-intro-to-reflection.lagda::*Our%20First%20Real%20Proof%20Tactic][Our First Real Proof Tactic:8]] -}
macro
  apply₂ : Term → Term → TC ⊤
  apply₂ p goal = try unify goal (def (quote sym)  (𝓋𝓇𝒶 p ∷ []))
                  or-else unify goal p

_ : {A : Set} (x y : A) → x ≡ y → (y ≡ x) × (x ≡ y)
_ = λ x y p → apply₂ p , apply₂ p
{- Our First Real Proof Tactic:8 ends here -}

{- [[file:~/reflection/gentle-intro-to-reflection.lagda::*Our%20First%20Real%20Proof%20Tactic][Our First Real Proof Tactic:9]] -}
macro
  apply₃ : Term → Term → TC ⊤
  apply₃ p goal = try unify goal (def (quote sym) (𝓋𝓇𝒶 p ∷ []))
                  or-else try unify goal p
                          or-else unify goal (con (quote refl) [])

yummah : {A : Set} {x y : A} (p : x ≡ y)  →  x ≡ y  ×  y ≡ x  ×  y ≡ y
yummah p = apply₃ p , apply₃ p , apply₃ p
{- Our First Real Proof Tactic:9 ends here -}

{- [[file:~/reflection/gentle-intro-to-reflection.lagda::*Our%20First%20Real%20Proof%20Tactic][Our First Real Proof Tactic:10]] -}
≡-type-info′ : Name → TC (Arg Term × Arg Term × Term × Term)
≡-type-info′ n = do τ ← getType n; ≡-type-info τ

macro
  sumSides : Name → Term → TC ⊤
  sumSides n goal = do _ , _ , l , r ← ≡-type-info′ n; unify goal (def (quote _+_) (𝓋𝓇𝒶 l ∷ 𝓋𝓇𝒶 r ∷ []))

_ : sumSides 𝓆 ≡ 𝓍 + 2 + 𝓎
_ = refl
{- Our First Real Proof Tactic:10 ends here -}

{- [[file:~/reflection/gentle-intro-to-reflection.lagda::*Our%20First%20Real%20Proof%20Tactic][Our First Real Proof Tactic:11]] -}
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
{- Our First Real Proof Tactic:11 ends here -}

{- [[file:~/reflection/gentle-intro-to-reflection.lagda::*Heuristic%20for%20Writing%20a%20Macro][Heuristic for Writing a Macro:1]] -}
{- If we have “f $ args” return “f”. -}
$-head : Term → Term
$-head (var v args) = var v []
$-head (con c args) = con c []
$-head (def f args) = def f []
$-head (pat-lam cs args) = pat-lam cs []
$-head t = t
{- Heuristic for Writing a Macro:1 ends here -}

{- [[file:~/reflection/gentle-intro-to-reflection.lagda::*Heuristic%20for%20Writing%20a%20Macro][Heuristic for Writing a Macro:2]] -}
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
{- Heuristic for Writing a Macro:2 ends here -}

{- [[file:~/reflection/gentle-intro-to-reflection.lagda::*Heuristic%20for%20Writing%20a%20Macro][Heuristic for Writing a Macro:3]] -}
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
{- Heuristic for Writing a Macro:3 ends here -}

{- [[file:~/reflection/gentle-intro-to-reflection.lagda::*What%20about%20somewhere%20deep%20within%20a%20subexpression?][What about somewhere deep within a subexpression?:1]] -}
{- +-suc : ∀ m n → m + suc n ≡ suc (m + n) -}

test₀ : ∀ {m n k : ℕ} → k + (m + suc n) ≡ k + suc (m + n)
test₀ {m} {n} {k} = cong (k +_) (+-suc m n)
{- What about somewhere deep within a subexpression?:1 ends here -}

{- [[file:~/reflection/gentle-intro-to-reflection.lagda::*What%20about%20somewhere%20deep%20within%20a%20subexpression?][What about somewhere deep within a subexpression?:2]] -}
postulate 𝒳 : ℕ
postulate 𝒢 : suc 𝒳 + (𝒳 * suc 𝒳 + suc 𝒳)  ≡  suc 𝒳 + suc (𝒳 * suc 𝒳 + 𝒳)

𝒮𝒳 : Arg Term
𝒮𝒳 = 𝓋𝓇𝒶 (con (quote suc) [ 𝓋𝓇𝒶 (quoteTerm 𝒳) ])

𝒢ˡ 𝒢ʳ : Term
𝒢ˡ = def (quote _+_) (𝒮𝒳 ∷ 𝓋𝓇𝒶 (def (quote _+_) (𝓋𝓇𝒶 (def (quote _*_) (𝓋𝓇𝒶 (quoteTerm 𝒳) ∷ 𝒮𝒳 ∷ [])) ∷ 𝒮𝒳 ∷ [])) ∷ [])
𝒢ʳ = def (quote _+_) (𝒮𝒳 ∷ 𝓋𝓇𝒶 (con (quote suc) [ 𝓋𝓇𝒶 (def (quote _+_) (𝓋𝓇𝒶 (def (quote _*_) (𝓋𝓇𝒶 (quoteTerm 𝒳) ∷ 𝒮𝒳 ∷ [])) ∷ 𝓋𝓇𝒶 (quoteTerm 𝒳) ∷ [])) ]) ∷ [])
{- What about somewhere deep within a subexpression?:2 ends here -}

{- [[file:~/reflection/gentle-intro-to-reflection.lagda::*What%20about%20somewhere%20deep%20within%20a%20subexpression?][What about somewhere deep within a subexpression?:3]] -}
{- Should definitily be in the standard library -}
⌊_⌋ : ∀ {a} {A : Set a} → Dec A → Bool
⌊ yes p ⌋ = true
⌊ no ¬p ⌋ = false


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
{- What about somewhere deep within a subexpression?:3 ends here -}

{- [[file:~/reflection/gentle-intro-to-reflection.lagda::*What%20about%20somewhere%20deep%20within%20a%20subexpression?][What about somewhere deep within a subexpression?:4]] -}
_ : 𝒢ˡ ⊓ 𝒢ʳ ≡ def (quote _+_) (𝒮𝒳 ∷ 𝓋𝓇𝒶 unknown ∷ [])
_ = refl

{- test using argument function 𝒶 and argument number X -}
_ : {X : ℕ} {𝒶 : ℕ → ℕ}
  →
    let gl = quoteTerm (𝒶 X + (X * 𝒶 X + 𝒶 X))
        gr = quoteTerm (𝒶 X + 𝒶 (X * 𝒶 X + X))
    in gl ⊓ gr ≡ def (quote _+_) (𝓋𝓇𝒶 (var 0 [ 𝓋𝓇𝒶 (var 1 []) ]) ∷ 𝓋𝓇𝒶 unknown ∷ [])
_ = refl
{- What about somewhere deep within a subexpression?:4 ends here -}

{- [[file:~/reflection/gentle-intro-to-reflection.lagda::*What%20about%20somewhere%20deep%20within%20a%20subexpression?][What about somewhere deep within a subexpression?:5]] -}
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
{- What about somewhere deep within a subexpression?:5 ends here -}

{- [[file:~/reflection/gentle-intro-to-reflection.lagda::*What%20about%20somewhere%20deep%20within%20a%20subexpression?][What about somewhere deep within a subexpression?:6]] -}
macro
  spine : Term → Term → TC ⊤
  spine p goal
    = do τ ← inferType p
         _ , _ , l , r ← ≡-type-info τ
         unify goal (patch (l ⊓ r))
{- What about somewhere deep within a subexpression?:6 ends here -}

{- [[file:~/reflection/gentle-intro-to-reflection.lagda::*What%20about%20somewhere%20deep%20within%20a%20subexpression?][What about somewhere deep within a subexpression?:7]] -}
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
{- What about somewhere deep within a subexpression?:7 ends here -}

{- [[file:~/reflection/gentle-intro-to-reflection.lagda::*What%20about%20somewhere%20deep%20within%20a%20subexpression?][What about somewhere deep within a subexpression?:8]] -}
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
{- What about somewhere deep within a subexpression?:8 ends here -}

{- [[file:~/reflection/gentle-intro-to-reflection.lagda::*What%20about%20somewhere%20deep%20within%20a%20subexpression?][What about somewhere deep within a subexpression?:9]] -}
macro
  apply₅ : Term → Term → TC ⊤
  apply₅ p hole
    = do τ ← inferType hole
         _ , _ , l , r ← ≡-type-info τ
         unify hole ((def (quote cong)
              (𝓋𝓇𝒶 (patch (l ⊓ r)) ∷ 𝓋𝓇𝒶 p ∷ [])))
{- What about somewhere deep within a subexpression?:9 ends here -}

{- [[file:~/reflection/gentle-intro-to-reflection.lagda::*What%20about%20somewhere%20deep%20within%20a%20subexpression?][What about somewhere deep within a subexpression?:10]] -}
_ : suc 𝒳 + (𝒳 * suc 𝒳 + suc 𝒳)  ≡  suc 𝒳 + suc (𝒳 * suc 𝒳 + 𝒳)
_ = apply₅ (+-suc (𝒳 * suc 𝒳) 𝒳)

test : ∀ {m n k : ℕ} → k + (m + suc n) ≡ k + suc (m + n)
test {m} {n} {k} = apply₅ (+-suc m n)
{- What about somewhere deep within a subexpression?:10 ends here -}
