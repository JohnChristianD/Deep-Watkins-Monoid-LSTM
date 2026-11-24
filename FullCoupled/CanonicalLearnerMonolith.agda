{-# OPTIONS
--lossy-unification
--syntactic-equality=1
--exact-split
--omega-in-omega
--rewriting
--confluence-check
--erased-quotient
#-}

module FullCoupled.CanonicalLearnerMonolith where

------------------------------------------------------------------------
-- Q8.24 scalar recurrent actor-critic.
--
-- One recurrent feature unit, a categorical actor head, and per-action
-- scalar Q values. The policy is a normalized positive linear preference
-- model. The implementation is intentionally small and scalar.
------------------------------------------------------------------------

open import Haskell.Prelude public
open import Haskell.Data.Int public
open import Haskell.Data.Bits public
open import Agda.Builtin.Equality.Rewrite public
open import Agda.Builtin.Strict public

postulate
  Domain  : Set₁
  ⟪_⟫     : Domain → Set

variable
  A B C   : Set
  D E F   : Domain
  n       : Nat

------------------------------------------------------------------------
-- Domains

postulate
  ⊥ : ⟪ D ⟫  -- bottom element

------------------------------------------------------------------------
-- Function domains

postulate
  _→ᶜ_     : Domain → Domain → Domain      -- assume continuous
  _→ˢ_     : Set    → Domain → Domain      -- always continuous
  dom-cts  : ⟪ D →ᶜ E ⟫ ≡ (⟪ D ⟫ → ⟪ E ⟫)
  set-cts  : ⟪ A →ˢ E ⟫ ≡ (A → ⟪ E ⟫)

{-# REWRITE dom-cts set-cts #-}

postulate
  fix : ⟪ (D →ᶜ D) →ᶜ D ⟫  -- fixed point of endofunction

------------------------------------------------------------------------
-- Flat domains

postulate
  _+⊥    : Set → Domain               -- lifted set
  η      : ⟪ A →ˢ A +⊥ ⟫              -- inclusion
  _♯     : ⟪ (A →ˢ D) →ᶜ A +⊥ →ᶜ D ⟫  -- Kleisli extension

Bool⊥    = Bool +⊥                    -- truth value domain
Nat⊥     = Nat +⊥                     -- natural number domain
String⊥  = String +⊥                  -- meta-string domain

postulate
  _==⊥_  : ⟪ Nat⊥ →ᶜ Nat →ˢ Bool⊥ ⟫   -- strict numerical equality
  _>=⊥_  : ⟪ Nat⊥ →ᶜ Nat →ˢ Bool⊥ ⟫   -- strict greater or equal
  _⟶_,_  : ⟪ Bool⊥ →ᶜ D →ᶜ D →ᶜ D ⟫   -- McCarthy conditional

------------------------------------------------------------------------
-- Sum domains

postulate
  _+_    : Domain → Domain → Domain                 -- separated sum
  inj₁   : ⟪ D →ᶜ D + E ⟫                            -- injection
  inj₂   : ⟪ E →ᶜ D + E ⟫                            -- injection
  [_,_]  : ⟪ (D →ᶜ F) →ᶜ (E →ᶜ F) →ᶜ (D + E →ᶜ F) ⟫  -- case analysis

------------------------------------------------------------------------
-- Product domains

postulate
  _×_   : Domain → Domain → Domain   -- cartesian product
  _,_   : ⟪ D →ᶜ E →ᶜ D × E ⟫         -- pairing
  _↓²1  : ⟪ D × E →ᶜ D ⟫              -- 1st projection
  _↓²2  : ⟪ D × E →ᶜ E ⟫              -- 2nd projection
  _↓³1  : ⟪ D × E × F →ᶜ D ⟫          -- 1st projection
  _↓³2  : ⟪ D × E × F →ᶜ E ⟫          -- 2nd projection
  _↓³3  : ⟪ D × E × F →ᶜ F ⟫          -- 3rd projection

------------------------------------------------------------------------
-- Tuple domains

_^_ : Domain → Nat → Domain        -- D ^ n  n-tuples
D ^ 0            = ⊤ +⊥ 
D ^ 1            = D
D ^ suc (suc n)  = D × (D ^ suc n)

------------------------------------------------------------------------
-- Finite sequence domains

postulate
  _⋆     : Domain → Domain         -- D ⋆ domain of finite sequences 
  ⟨⟩     : ⟪ D ⋆ ⟫                 -- empty sequence
  ⟨_⟩    : ⟪ (D ^ suc n) →ᶜ D ⋆ ⟫  -- ⟨ d₁ , ... , dₙ₊₁ ⟩ non-empty sequence
  #      : ⟪ D ⋆ →ᶜ Nat⊥ ⟫         -- # d⋆                sequence length
  _§_    : ⟪ D ⋆ →ᶜ D ⋆ →ᶜ D ⋆ ⟫   -- d⋆ § d⋆             concatenation
  _↓_    : ⟪ D ⋆ →ᶜ Nat →ˢ D ⟫     -- d⋆ ↓ n              nth component
  _†_    : ⟪ D ⋆ →ᶜ Nat →ˢ D ⋆ ⟫   -- d⋆ † n              nth tail

------------------------------------------------------------------------
-- Grouping precedence

infixr 0  _→ᶜ_
infixr 0  _→ˢ_
infixr 1   _+_
infixr 2   _×_
infixr 4   _,_
infix  8   _^_
infix  10   _+⊥
infixr 20  _⟶_,_

-- ⟦_⟧ = id


-- An abandoned effort
-- This is subsumed by the other modules
-- Therefore I am justified to not leave any more explanation here

module Syntax where

data ± : Set where
    + : ±
    - : ±

data 𝕋 : ± -> Set where
    _⊗_ : 𝕋 + -> 𝕋 + -> 𝕋 +
    _⊕_ : 𝕋 + -> 𝕋 + -> 𝕋 +
    _&_ : 𝕋 - -> 𝕋 - -> 𝕋 -
    _⅋_ : 𝕋 - -> 𝕋 - -> 𝕋 -
    𝟙 : 𝕋 +
    𝟘 : 𝕋 +
    ⊤ : 𝕋 -
    ⊥ : 𝕋 -
    ↑_ : 𝕋 + -> 𝕋 -
    ↓_ : 𝕋 - -> 𝕋 +
    ¬⁺_ : 𝕋 + -> 𝕋 +
    ¬⁻_ : 𝕋 - -> 𝕋 -

infixl 8 _⊗_
infixl 8 _⊕_
infixl 8 _&_
infixl 8 _⅋_

infix 9 ↑_
infix 9 ↓_
infix 9 ¬⁺_
infix 9 ¬⁻_

data T : Set where
    ▹ : ∀ {p} -> 𝕋 p -> T
    ◃ : ∀ {p} -> 𝕋 p -> T

data J : Set where
    :- : T -> J
    # : J

data Pattern : ∀ p -> 𝕋 p -> Set where
    ⟨_,_⟩ : ∀ {A B} -> Pattern + A -> Pattern + B -> Pattern + (A ⊗ B)
    ϖ₁ : ∀ {A B} -> Pattern + A -> Pattern + (A ⊕ B)
    ϖ₂ : ∀ {A B} -> Pattern + B -> Pattern + (A ⊕ B)
    ⟪_,_⟫ : ∀ {A B} -> Pattern - A -> Pattern - B -> Pattern - (A ⅋ B)
    π₁ : ∀ {A B} -> Pattern - A -> Pattern - (A & B)
    π₂ : ∀ {A B} -> Pattern - B -> Pattern - (A & B)
    *̂ : Pattern + 𝟙
    *̬ : Pattern - ⊥
    ⇑ : ∀ { A : 𝕋 + } -> Pattern - (↑ A)
    ⇓ : ∀ { A : 𝕋 - } -> Pattern + (↓ A)
    ●⁺ : ∀ { A : 𝕋 + } -> Pattern + (¬⁺ A)
    ●⁻ : ∀ { A : 𝕋 - } -> Pattern - (¬⁻ A)

data _∋̂_ : ∀ {p A} -> Pattern p A -> T -> Set where
    ⟨_,~⟩ : ∀ {A B t} {p : Pattern + A} {q : Pattern + B} -> p ∋̂ t -> ⟨ p , q ⟩ ∋̂ t
    ⟨~,_⟩ : ∀ {A B t} {p : Pattern + A} {q : Pattern + B} -> q ∋̂ t -> ⟨ p , q ⟩ ∋̂ t
    ~ϖ₁ : ∀ {A B t} {p : Pattern + A} -> p ∋̂ t -> ϖ₁ {B = B} p ∋̂ t
    ~ϖ₂ : ∀ {A B t} {p : Pattern + B} -> p ∋̂ t -> ϖ₂ {A = A} p ∋̂ t
    ⟪_,~⟫ : ∀ {A B t} {p : Pattern - A} {q : Pattern - B} -> p ∋̂ t -> ⟪ p , q ⟫ ∋̂ t
    ⟪~,_⟫ : ∀ {A B t} {p : Pattern - A} {q : Pattern - B} -> q ∋̂ t -> ⟪ p , q ⟫ ∋̂ t
    ~π₁ : ∀ {A B t} {p : Pattern - A} -> p ∋̂ t -> π₁ {B = B} p ∋̂ t
    ~π₂ : ∀ {A B t} {p : Pattern - B} -> p ∋̂ t -> π₂ {A = A} p ∋̂ t
    ~⇑ : ∀ { A : 𝕋 + } -> ⇑ {A} ∋̂ ▹ A
    ~⇓ : ∀ { A : 𝕋 - } -> ⇓ {A} ∋̂ ◃ A
    ~●⁺ : ∀ {A} -> ●⁺ {A} ∋̂ ◃ A
    ~●⁻ : ∀ {A} -> ●⁻ {A} ∋̂ ▹ A

infix 6 _∋̂_

-- Contexts should respect the structure of bindings
-- Everyone got to be somewhere!

-- Records the Occurence
data Occurs : ∀ {p A} -> Pattern p A -> Set where
    ^⟨_,_⟩ : ∀ {A B} {p : Pattern _ A} {q : Pattern _ B} -> Occurs p -> Occurs q -> Occurs ⟨ p , q ⟩
    ^ϖ₁ : ∀ {A B} {p : Pattern _ A} -> Occurs p -> Occurs (ϖ₁ {B = B} p)
    ^ϖ₂ : ∀ {A B} {p : Pattern _ B} -> Occurs p -> Occurs (ϖ₂ {A = A} p)
    ^⟪_,_⟫ : ∀ {A B} {p : Pattern _ A} {q : Pattern _ B} -> Occurs p -> Occurs q -> Occurs ⟪ p , q ⟫
    ^π₁ : ∀ {A B} {p : Pattern _ A} -> Occurs p -> Occurs (π₁ {B = B} p)
    ^π₂ : ∀ {A B} {p : Pattern _ B} -> Occurs p -> Occurs (π₂ {A = A} p)
    ^*̂ : Occurs *̂
    ^*̬ : Occurs *̬
    □⇑ : ∀ { A : 𝕋 + } -> Occurs (⇑ {A})
    ■⇑ : ∀ { A : 𝕋 + } -> Occurs (⇑ {A})
    □●⁺ : ∀ { A : 𝕋 + } -> Occurs (●⁺ {A})
    ■●⁺ : ∀ { A : 𝕋 + } -> Occurs (●⁺ {A})
    □⇓ : ∀ { A : 𝕋 - } -> Occurs (⇓ {A})
    ■⇓ : ∀ { A : 𝕋 - } -> Occurs (⇓ {A})
    □●⁻ : ∀ { A : 𝕋 - } -> Occurs (●⁻ {A})
    ■●⁻ : ∀ { A : 𝕋 - } -> Occurs (●⁻ {A})

-- Disjoint union of occurrences
data _⊎_≅_ : ∀ {pol A}{p : Pattern pol A} -> Occurs p -> Occurs p -> Occurs p -> Set where
    ⊎⟨_,_⟩ : ∀{A B}{ p : Pattern _ A }{ q : Pattern _ B }{ Δ₁ Δ₂ Δ₃ : Occurs p }{ Γ₁ Γ₂ Γ₃ : Occurs q}
        -> Δ₁ ⊎ Δ₂ ≅ Δ₃ -> Γ₁ ⊎ Γ₂ ≅ Γ₃ -> ^⟨ Δ₁ , Γ₁ ⟩ ⊎ ^⟨ Δ₂ , Γ₂ ⟩ ≅ ^⟨ Δ₃ , Γ₃ ⟩
    ⊎ϖ₁ : ∀{A B}{ p : Pattern + A }{ Δ₁ Δ₂ Δ₃ : Occurs p }
        -> Δ₁ ⊎ Δ₂ ≅ Δ₃ -> ^ϖ₁ Δ₁ ⊎ ^ϖ₁ Δ₂ ≅ ^ϖ₁ {B = B} Δ₃
    ⊎ϖ₂ : ∀{A B}{ p : Pattern + B }{ Δ₁ Δ₂ Δ₃ : Occurs p }
        -> Δ₁ ⊎ Δ₂ ≅ Δ₃ -> ^ϖ₂ Δ₁ ⊎ ^ϖ₂ Δ₂ ≅ ^ϖ₂ {A = A} Δ₃
    ⊎⟪_,_⟫ : ∀{A B}{ p : Pattern _ A }{ q : Pattern _ B }{ Δ₁ Δ₂ Δ₃ : Occurs p }{ Γ₁ Γ₂ Γ₃ : Occurs q}
        -> Δ₁ ⊎ Δ₂ ≅ Δ₃ -> Γ₁ ⊎ Γ₂ ≅ Γ₃ -> ^⟪ Δ₁ , Γ₁ ⟫ ⊎ ^⟪ Δ₂ , Γ₂ ⟫ ≅ ^⟪ Δ₃ , Γ₃ ⟫
    ⊎π₁ : ∀{A B}{ p : Pattern - A }{ Δ₁ Δ₂ Δ₃ : Occurs p }
        -> Δ₁ ⊎ Δ₂ ≅ Δ₃ -> ^π₁ Δ₁ ⊎ ^π₁ Δ₂ ≅ ^π₁ {B = B} Δ₃
    ⊎π₂ : ∀{A B}{ p : Pattern - B }{ Δ₁ Δ₂ Δ₃ : Occurs p }
        -> Δ₁ ⊎ Δ₂ ≅ Δ₃ -> ^π₂ Δ₁ ⊎ ^π₂ Δ₂ ≅ ^π₂ {A = A} Δ₃
    ⊎*̂ : ^*̂ ⊎ ^*̂ ≅ ^*̂
    ⊎*̬ : ^*̬ ⊎ ^*̬ ≅ ^*̬
    ⊎⇑L : ∀{A} -> ■⇑ ⊎ □⇑ ≅ ■⇑ {A}
    ⊎⇑R : ∀{A} -> □⇑ ⊎ ■⇑ ≅ ■⇑ {A}
    ⊎⇑□ : ∀{A} -> □⇑ ⊎ □⇑ ≅ □⇑ {A}
    ⊎⇓L : ∀{A} -> ■⇓ ⊎ □⇓ ≅ ■⇓ {A}
    ⊎⇓R : ∀{A} -> □⇓ ⊎ ■⇓ ≅ ■⇓ {A}
    ⊎⇓□ : ∀{A} -> □⇓ ⊎ □⇓ ≅ □⇓ {A}
    ⊎●⁺L : ∀{A} -> ■●⁺ ⊎ □●⁺ ≅ ■●⁺ {A}
    ⊎●⁺R : ∀{A} -> □●⁺ ⊎ ■●⁺ ≅ ■●⁺ {A}
    ⊎●⁺□ : ∀{A} -> □●⁺ ⊎ □●⁺ ≅ □●⁺ {A}
    ⊎●⁻L : ∀{A} -> ■●⁻ ⊎ □●⁻ ≅ ■●⁻ {A}
    ⊎●⁻R : ∀{A} -> □●⁻ ⊎ ■●⁻ ≅ ■●⁻ {A}
    ⊎●⁻□ : ∀{A} -> □●⁻ ⊎ □●⁻ ≅ □●⁻ {A}

-- Auxiliary functions to construct occurrences
■ : ∀ {pol A} -> (p : Pattern pol A) -> Occurs p
■ ⟨ p , q ⟩ = ^⟨ ■ p , ■ q ⟩
■ (ϖ₁ p) = ^ϖ₁ (■ p)
■ (ϖ₂ p) = ^ϖ₂ (■ p)
■ ⟪ p , q ⟫ = ^⟪ ■ p , ■ q ⟫
■ (π₁ p) = ^π₁ (■ p)
■ (π₂ p) = ^π₂ (■ p)
■ *̂ = ^*̂
■ *̬ = ^*̬
■ ⇑ = ■⇑
■ ⇓ = ■⇓
■ ●⁺ = ■●⁺
■ ●⁻ = ■●⁻

□ : ∀ {pol A} -> (p : Pattern pol A) -> Occurs p
□ ⟨ p , q ⟩ = ^⟨ □ p , □ q ⟩
□ (ϖ₁ p) = ^ϖ₁ (□ p)
□ (ϖ₂ p) = ^ϖ₂ (□ p)
□ ⟪ p , q ⟫ = ^⟪ □ p , □ q ⟫
□ (π₁ p) = ^π₁ (□ p)
□ (π₂ p) = ^π₂ (□ p)
□ *̂ = ^*̂
□ *̬ = ^*̬
□ ⇑ = □⇑
□ ⇓ = □⇓
□ ●⁺ = □●⁺
□ ●⁻ = □●⁻


focus : ∀ {pol A B} -> (p : Pattern pol A) -> p ∋̂ B -> Occurs p
focus ⟨ p , q ⟩ ⟨ α ,~⟩ = ^⟨ focus p α , □ q ⟩
focus ⟨ p , q ⟩ ⟨~, α ⟩ = ^⟨ □ p , focus q α ⟩
focus (ϖ₁ p) (~ϖ₁ α) = ^ϖ₁ (focus p α)
focus (ϖ₂ p) (~ϖ₂ α) = ^ϖ₂ (focus p α)
focus ⟪ p , q ⟫ ⟪ α ,~⟫ = ^⟪ (focus p α) , □ q ⟫
focus ⟪ p , q ⟫ ⟪~, α ⟫ = ^⟪ □ p , (focus q α) ⟫
focus (π₁ p) (~π₁ α) = ^π₁ (focus p α)
focus (π₂ p) (~π₂ α) = ^π₂ (focus p α)
focus ⇑ ~⇑ = ■⇑
focus ⇓ ~⇓ = ■⇓
focus ●⁺ ~●⁺ = ■●⁺
focus ●⁻ ~●⁻ = ■●⁻


-- Now we can properly write some linear code
-- Contexts indicates usage while Stack doesn't

data Stack : Set where
    ∅ : Stack
    _∶_ : ∀ {pol A} -> Stack -> Pattern pol A -> Stack

data Context : Stack -> Set where
    ε : Context ∅
    _∷_ : ∀ {pol A}{p : Pattern pol A}{Σ} -> Context Σ -> Occurs p -> Context (Σ ∶ p)

infix 6 _⊎_≅_
infixl 6 _∷_ _∶_
infix 5 _⊎⊎_≅≅_

-- Extend ⊎ to contexts
data _⊎⊎_≅≅_ : ∀ {Σ} -> Context Σ -> Context Σ -> Context Σ -> Set where
    ⊎⊎ε : ε ⊎⊎ ε ≅≅ ε
    ⊎⊎∷ : ∀ {Σ pol A} {p : Pattern pol A} {Γ₁ Γ₂ Γ₃ : Context Σ} {Δ₁ Δ₂ Δ₃ : Occurs p}
        -> Γ₁ ⊎⊎ Γ₂ ≅≅ Γ₃ -> Δ₁ ⊎ Δ₂ ≅ Δ₃
        -> Γ₁ ∷ Δ₁ ⊎⊎ Γ₂ ∷ Δ₂ ≅≅ Γ₃ ∷ Δ₃

-- Extend □ to contexts
□̂ : ∀ Σ -> Context Σ
□̂ ∅ = ε
□̂ (Σ ∶ α) = (□̂ Σ) ∷ □ α

■̂ : ∀ Σ -> Context Σ
■̂ ∅ = ε
■̂ (Σ ∶ α) = (■̂ Σ) ∷ ■ α

infix 5 _∋_

data _∋_ : ∀ {Σ} -> Context Σ -> T -> Set where
    ŝ_ : ∀ {Σ pol'} {A : T} {B : 𝕋 pol'} {p} {Γ : Context Σ} {Δ}
        -> Γ ∋ A -> (_∷_ {A = B} {p = p} Γ Δ) ∋ A
    ẑ_ : ∀ {Σ pol'} {A : T} {B : 𝕋 pol'} {p}
        -> (α : p ∋̂ A) -> (_∷_ {A = B} {p = p} (□̂ Σ) (focus p α)) ∋ A

infixr 9 ŝ_ ẑ_

-- Sanity Check
𝔹 : 𝕋 +
𝔹 = (𝟙 ⊕ 𝟙)

𝕗 : Pattern + 𝔹
𝕗 = ϖ₁ *̂

𝕥 : Pattern + 𝔹
𝕥 = ϖ₂ *̂

-- For the normal terms!
data _⊨_ : ∀ {Σ} -> Context Σ -> J -> Set
data _⊨⊨_ : ∀ {Σ} -> Context Σ -> ∀ {pol A} (p : Pattern pol A) -> Set

infix 5 _⊨_ _⊨⊨_

data _⊨_ where
    _⟦_⟧⁺ : ∀ {Σ} {Γ : Context Σ} { A : 𝕋 + }
        -> (Δ : Pattern + A)
        -> Γ ⊨⊨ Δ
        -> Γ ⊨ :- (▹ A)
    _⟦_⟧⁻ : ∀ {Σ} {Γ : Context Σ} { A : 𝕋 - }
        -> (Δ : Pattern - A)
        -> Γ ⊨⊨ Δ
        -> Γ ⊨ :- (◃ A)
    case⁺ : ∀ {Σ} {Γ : Context Σ} { A : 𝕋 + }
        -> ((Δ : Pattern + A) -> (Γ ∷ ■ Δ) ⊨ #)
        -> Γ ⊨ :- (◃ A)
    case⁻ : ∀ {Σ} {Γ : Context Σ} { A : 𝕋 - }
        -> ((Δ : Pattern - A) -> (Γ ∷ ■ Δ) ⊨ #)
        -> Γ ⊨ :- (▹ A)
    var : ∀ {Σ} {Γ : Context Σ} { A : T }
        -> Γ ∋ A -> Γ ⊨ :- A
    _#⁺_ : ∀ {Σ} {Γ Γ* Γ' : Context Σ} { A : 𝕋 + }
        -> {σ : Γ ⊎⊎ Γ* ≅≅ Γ'}
        -> (v⁺ : Γ* ∋ ◃ A)
        -> Γ ⊨ :- (▹ A)
        -> Γ' ⊨ #
    _#⁻_ : ∀ {Σ} {Γ Γ* Γ' : Context Σ} { A : 𝕋 - }
        -> {σ : Γ ⊎⊎ Γ* ≅≅ Γ'}
        -> (v⁻ : Γ* ∋ ▹ A)
        -> Γ ⊨ :- (◃ A)
        -> Γ' ⊨ #

infix 6 _#⁺_ _#⁻_
infix 7 _⟦_⟧⁺ _⟦_⟧⁻

data _⊨⊨_ where  -- Just Pattern -> _⊨_
    ⊨⊨*̂ : ∀ {Σ} -> □̂ Σ ⊨⊨ *̂
    ⊨⊨*̬ : ∀ {Σ} -> □̂ Σ ⊨⊨ *̬
    ⊨⊨⇑ : ∀ {Σ A⁺} {Γ : Context Σ}
        -> Γ ⊨ :- (◃ A⁺) -> Γ ⊨⊨ ⇑ {A = A⁺}
    ⊨⊨⇓ : ∀ {Σ A⁻} {Γ : Context Σ}
        -> Γ ⊨ :- (▹ A⁻) -> Γ ⊨⊨ ⇓ {A = A⁻}
    ⊨⊨●⁺ : ∀ {Σ A⁺} {Γ : Context Σ}
        -> Γ ⊨ :- (◃ A⁺) -> Γ ⊨⊨ ●⁺ {A = A⁺}
    ⊨⊨●⁻ : ∀ {Σ A⁻} {Γ : Context Σ}
        -> Γ ⊨ :- (▹ A⁻) -> Γ ⊨⊨ ●⁻ {A = A⁻}
    ⊨⊨⟨_,_⟩ : ∀ {Σ} {Γ₁ Γ₂ Γ₃ : Context Σ} {A⁺ B⁺} {p : Pattern + A⁺} {q : Pattern + B⁺}
        -> {Γ₁ ⊎⊎ Γ₂ ≅≅ Γ₃}
        -> Γ₁ ⊨⊨ p -> Γ₂ ⊨⊨ q -> Γ₃ ⊨⊨ ⟨ p , q ⟩
    ⊨⊨⟪_,_⟫ : ∀ {Σ} {Γ₁ Γ₂ Γ₃ : Context Σ} {A⁻ B⁻} {p : Pattern - A⁻} {q : Pattern - B⁻}
        -> {Γ₁ ⊎⊎ Γ₂ ≅≅ Γ₃}
        -> Γ₁ ⊨⊨ p -> Γ₂ ⊨⊨ q -> Γ₃ ⊨⊨ ⟪ p , q ⟫
    ⊨⊨ϖ₁ : ∀ {Σ} {Γ : Context Σ} {A⁺ B⁺} {p : Pattern + A⁺}
        -> Γ ⊨⊨ p -> Γ ⊨⊨ ϖ₁ {B = B⁺} p
    ⊨⊨ϖ₂ : ∀ {Σ} {Γ : Context Σ} {A⁺ B⁺} {p : Pattern + B⁺}
        -> Γ ⊨⊨ p -> Γ ⊨⊨ ϖ₂ {A = A⁺} p
    ⊨⊨π₁ : ∀ {Σ} {Γ : Context Σ} {A⁻ B⁻} {p : Pattern - A⁻}
        -> Γ ⊨⊨ p -> Γ ⊨⊨ π₁ {B = B⁻} p
    ⊨⊨π₂ : ∀ {Σ} {Γ : Context Σ} {A⁻ B⁻} {p : Pattern - B⁻}
        -> Γ ⊨⊨ p -> Γ ⊨⊨ π₂ {A = A⁻} p

-- Some example terms

tt : ε ⊨ :- (▹ 𝔹)
tt = 𝕥 ⟦ ⊨⊨ϖ₂ ⊨⊨*̂ ⟧⁺

ff : ε ⊨ :- (▹ 𝔹)
ff = 𝕗 ⟦ ⊨⊨ϖ₁ ⊨⊨*̂ ⟧⁺

not : ε ∷ (■ (●⁺ {A = 𝔹})) ⊨ :- (◃ 𝔹)
not = case⁺ n
    where
        n : (b : Pattern + 𝔹) → ε ∷ ■●⁺ ∷ ■ b ⊨ #
        n (ϖ₁ *̂) = _#⁺_
            {σ = ⊎⊎∷ (⊎⊎∷ ⊎⊎ε ⊎●⁺R) (⊎ϖ₁ ⊎*̂)}
            (ŝ ẑ ~●⁺) (𝕥 ⟦ ⊨⊨ϖ₂ ⊨⊨*̂ ⟧⁺)
        n (ϖ₂ *̂) = _#⁺_
            {σ = ⊎⊎∷ (⊎⊎∷ ⊎⊎ε ⊎●⁺R) (⊎ϖ₂ ⊎*̂)}
            (ŝ ẑ ~●⁺) (𝕗 ⟦ ⊨⊨ϖ₁ ⊨⊨*̂ ⟧⁺)



qShift : Int
qShift = 24

qOne qHalf qQuarter qTwo : Int32
qOne     = 16777216
qHalf    = 8388608
qQuarter = 4194304
qTwo     = 33554432

qMax64 qMin64 : Int64
qMax64 = 2147483647
qMin64 = -2147483648

qBeta qEpsilon qGamma : Int32
qBeta    = 16609444
qEpsilon = 65536
qGamma   = 16609444

qFrom64 : Int64 -> Int32
qFrom64 x =
  fromIntegral
    (if qMax64 < x then qMax64
     else if x < qMin64 then qMin64
     else x)

qAdd : Int32 -> Int32 -> Int32
qAdd x y = qFrom64 (fromIntegral x + fromIntegral y)

qSub : Int32 -> Int32 -> Int32
qSub x y = qFrom64 (fromIntegral x - fromIntegral y)

qNeg : Int32 -> Int32
qNeg x = qFrom64 (0 - fromIntegral x)

qClamp : Int32 -> Int32 -> Int32 -> Int32
qClamp x lo hi = if x < lo then lo else if hi < x then hi else x

qAbs : Int32 -> Int32
qAbs x = if x < 0 then qFrom64 (0 - fromIntegral x) else x

qMul : Int32 -> Int32 -> Int32
qMul x y =
  qFrom64
    (shiftR (fromIntegral x * fromIntegral y) qShift)

qDiv64 : Int32 -> Int64 -> Int32
qDiv64 numerator denominator =
  if denominator <= 0 then 0
  else
    qFrom64
      (quot (shiftL (fromIntegral numerator) qShift) denominator)

qDiv : Int32 -> Int32 -> Int32
qDiv numerator denominator =
  if denominator == 0 then 0
  else
    qFrom64
      (quot
        (shiftL (fromIntegral numerator) qShift)
        (fromIntegral denominator))

-- Q8.24 derivative of x / (1 + |x|).
qSoftsignGrad : Int32 -> Int32
qSoftsignGrad x =
  let denominator = fromIntegral qOne + fromIntegral (qAbs x)
      denominatorSquared = shiftR (denominator * denominator) qShift
  in qDiv64 qOne denominatorSquared

qSoftsign : Int32 -> Int32
qSoftsign x = qDiv x (qAdd qOne (qAbs x))

qRelu : Int32 -> Int32
qRelu x = if 0 < x then x else 0

-- Hard-sigmoid update gate: clamp(1/2 + x/4, 0, 1).
qHardSigmoid : Int32 -> Int32
qHardSigmoid x = qClamp (qAdd qHalf (qMul x qQuarter)) 0 qOne

qHardSigmoidGrad : Int32 -> Int32
qHardSigmoidGrad x =
  if qNeg qTwo < x && x < qTwo then qQuarter else 0

qSarsaOneStepTarget : Int32 -> Int32 -> Bool -> Int32
qSarsaOneStepTarget reward nextActionValue terminal =
  if terminal then reward
  else qAdd reward (qMul qGamma nextActionValue)

------------------------------------------------------------------------
-- Optimizer state and recurrent cell
------------------------------------------------------------------------

record StreamW : Set where
  constructor MkSW
  field
    streamWeight : Int32
    streamMaxGrad : Int32
open StreamW public

streamStep : StreamW -> Int32 -> Int32 -> Int32 -> StreamW
streamStep (MkSW weight maxGrad) delta input learningRate =
  let gradient = qMul delta input
      magnitude = qAbs gradient
      decayedMax = qMul qBeta maxGrad
      nextMax = if decayedMax < magnitude then magnitude else decayedMax
      denominator = qAdd nextMax qEpsilon
      update = qMul learningRate (qDiv gradient denominator)
      decay = shiftR weight 18
  in MkSW (qSub (qAdd weight update) decay) nextMax

record CellCache : Set where
  constructor MkCellCache
  field
    cellRaw : Int32
    cellHiddenBefore : Int32
    cellPreFeature : Int32
    cellFeature : Int32
    cellGateInput : Int32
    cellGate : Int32
    cellCandidateInput : Int32
    cellCandidate : Int32
    cellMixPre : Int32
    cellHiddenAfter : Int32
open CellCache public

cellForward : Int32 -> Int32 -> Int32 -> Int32 -> Int32 -> CellCache
cellForward raw hidden inputWeight candidateWeight gateWeight =
  let preFeature = qMul inputWeight raw
      feature = qSoftsign preFeature
      gateInput = qAdd feature (qMul gateWeight hidden)
      gate = qHardSigmoid gateInput
      candidateInput = qAdd feature (qMul candidateWeight hidden)
      candidate = qRelu candidateInput
      mixPre =
        qAdd
          (qMul (qSub qOne gate) hidden)
          (qMul gate candidate)
      hiddenAfter = qRelu mixPre
  in MkCellCache
       raw hidden preFeature feature gateInput gate
       candidateInput candidate mixPre hiddenAfter

record CellPullback : Set where
  constructor MkCellPullback
  field
    cellHiddenCotangent : Int32
    cellInputCotangent : Int32
    cellInputWeightCotangent : Int32
    cellCandidateWeightCotangent : Int32
    cellGateWeightCotangent : Int32
open CellPullback public

-- VJP of the smooth shadow of the quantized recurrent cell.
-- ReLU contributes its indicator derivative; Softsign is used only by
-- the input feature map and has its own derivative.
cellPullback :
  Int32 -> Int32 -> Int32 -> CellCache -> Int32 -> CellPullback
cellPullback inputWeight candidateWeight gateWeight cache hiddenCotangent =
  let gate = cellGate cache
      hidden = cellHiddenBefore cache
      candidate = cellCandidate cache
      mixCotangent = if 0 < cellMixPre cache then hiddenCotangent else 0
      candidateCotangent = qMul mixCotangent gate
      candidateInputCotangent =
        if 0 < cellCandidateInput cache then candidateCotangent else 0
      gateCotangent = qMul mixCotangent (qSub candidate hidden)
      gateInputCotangent =
        qMul gateCotangent (qHardSigmoidGrad (cellGateInput cache))
      featureCotangent = qAdd candidateInputCotangent gateInputCotangent
      preFeatureCotangent =
        qMul featureCotangent (qSoftsignGrad (cellPreFeature cache))
      inputCotangent = qMul preFeatureCotangent inputWeight
      inputWeightCotangent = qMul preFeatureCotangent (cellRaw cache)
      candidateWeightCotangent = qMul candidateInputCotangent hidden
      gateWeightCotangent = qMul gateInputCotangent hidden
      hiddenCotangentBefore =
        qAdd
          (qMul mixCotangent (qSub qOne gate))
          (qAdd
            (qMul candidateInputCotangent candidateWeight)
            (qMul gateInputCotangent gateWeight))
  in MkCellPullback
       hiddenCotangentBefore
       inputCotangent
       inputWeightCotangent
       candidateWeightCotangent
       gateWeightCotangent

------------------------------------------------------------------------
-- Functional lists used by action heads
------------------------------------------------------------------------

mapList : {A B : Set} -> (A -> B) -> List A -> List B
mapList f [] = []
mapList f (x ∷ xs) = f x ∷ mapList f xs

zipWithList : {A B C : Set} -> (A -> B -> C) -> List A -> List B -> List C
zipWithList f [] ys = []
zipWithList f xs [] = []
zipWithList f (x ∷ xs) (y ∷ ys) = f x y ∷ zipWithList f xs ys

sumQ : List Int32 -> Int32
sumQ = go 0
  where
    go : Int32 -> List Int32 -> Int32
    go total [] = total
    go total (x ∷ xs) = go (qAdd total x) xs

sumQ64 : List Int32 -> Int64
sumQ64 = go 0
  where
    go : Int64 -> List Int32 -> Int64
    go total [] = total
    go total (x ∷ xs) = go (total + fromIntegral x) xs

nthQ : Nat -> List Int32 -> Int32
nthQ zero (x ∷ xs) = x
nthQ (suc n) (x ∷ xs) = nthQ n xs
nthQ n [] = 0

natEqual : Nat -> Nat -> Bool
natEqual zero zero = true
natEqual zero (suc n) = false
natEqual (suc n) zero = false
natEqual (suc m) (suc n) = natEqual m n

streamValues : List StreamW -> List Int32
streamValues = mapList streamWeight

streamFromValues : List Int32 -> List StreamW
streamFromValues [] = []
streamFromValues (w ∷ ws) = MkSW w 0 ∷ streamFromValues ws

------------------------------------------------------------------------
-- Categorical policy: normalized positive linear preferences
------------------------------------------------------------------------

qPreference : Int32 -> Int32
qPreference logit =
  qAdd qQuarter (qAdd qOne (qClamp logit (qNeg qOne) qOne))

policyProbabilities : List Int32 -> List Int32
policyProbabilities logits =
  let preferences = mapList qPreference logits
      total = sumQ64 preferences
  in mapList (λ preference -> qDiv64 preference total) preferences

sampleAction : Int32 -> List Int32 -> Nat
sampleAction draw probabilities = go zero 0 zero probabilities
  where
    go : Nat -> Int32 -> Nat -> List Int32 -> Nat
    go index cumulative lastIndex [] = lastIndex
    go index cumulative lastIndex (probability ∷ rest) =
      let nextCumulative = qAdd cumulative probability
      in if qClamp draw 0 (qSub qOne 1) < nextCumulative
         then index
         else go (suc index) nextCumulative index rest

-- d log pi(action | h) / d logit(j), including preference-clamp derivative.
policyScoreFactors :
  Nat -> Int64 -> List Int32 -> List Int32 -> List Int32
policyScoreFactors action total = go zero
  where
    go : Nat -> List Int32 -> List Int32 -> List Int32
    go index [] prefs = []
    go index logits [] = []
    go index (logit ∷ logits) (preference ∷ preferences) =
      let active = qNeg qOne < logit && logit < qOne
          selected = if natEqual index action then qDiv64 qOne (fromIntegral preference) else 0
          normalizer = qDiv64 qOne total
          score = if active then qSub selected normalizer else 0
      in score ∷ go (suc index) logits preferences

record ActionHead : Set where
  constructor MkActionHead
  field
    actionActorWeight : StreamW
    actionCriticWeight : StreamW
open ActionHead public

-- Each action owns one actor/critic pair; empty and mismatched heads are unrepresentable.
record NonEmptyActionHeads : Set where
  constructor MkActionHeads
  field
    firstActionHead : ActionHead
    remainingActionHeads : List ActionHead
open NonEmptyActionHeads public

actionActorWeights : NonEmptyActionHeads -> List StreamW
actionActorWeights (MkActionHeads first rest) =
  actionActorWeight first ∷ mapList actionActorWeight rest

actionCriticWeights : NonEmptyActionHeads -> List StreamW
actionCriticWeights (MkActionHeads first rest) =
  actionCriticWeight first ∷ mapList actionCriticWeight rest

nthActionHead : Nat -> NonEmptyActionHeads -> ActionHead
nthActionHead zero (MkActionHeads first rest) = first
nthActionHead (suc n) (MkActionHeads first (next ∷ rest)) =
  nthActionHead n (MkActionHeads next rest)
nthActionHead (suc n) (MkActionHeads first []) = first


dropOne : {A : Set} -> List A -> List A
dropOne [] = []
dropOne (x ∷ xs) = xs

updateOneActionHead :
  Bool -> Int32 -> Int32 -> Int32 -> Int32 -> ActionHead -> ActionHead
updateOneActionHead selected actorDelta td hidden learningRate head =
  MkActionHead
    (streamStep (actionActorWeight head) actorDelta hidden learningRate)
    (if selected
     then streamStep (actionCriticWeight head) td hidden learningRate
     else actionCriticWeight head)

updateRemainingActionHeads :
  Nat -> Nat -> List ActionHead -> List Int32 ->
  Int32 -> Int32 -> Int32 -> List ActionHead
updateRemainingActionHeads action index [] factors td hidden learningRate = []
updateRemainingActionHeads action index (head ∷ rest) [] td hidden learningRate =
  updateOneActionHead (natEqual action index) 0 td hidden learningRate head
    ∷ updateRemainingActionHeads action (suc index) rest [] td hidden learningRate
updateRemainingActionHeads action index (head ∷ rest) (factor ∷ factors)
    td hidden learningRate =
  updateOneActionHead (natEqual action index) factor td hidden learningRate head
    ∷ updateRemainingActionHeads action (suc index) rest factors td hidden learningRate

updateAllActionHeads :
  Nat -> List Int32 -> Int32 -> Int32 -> Int32 -> NonEmptyActionHeads ->
  NonEmptyActionHeads
updateAllActionHeads action actorDeltas td hidden learningRate
    (MkActionHeads first rest) =
  MkActionHeads
    (updateOneActionHead (natEqual action zero) (nthQ zero actorDeltas)
      td hidden learningRate first)
    (updateRemainingActionHeads action (suc zero) rest (dropOne actorDeltas)
      td hidden learningRate)

------------------------------------------------------------------------
-- Recurrent actor-critic state and forward step
------------------------------------------------------------------------

record NetworkState : Set where
  constructor MkNetworkState
  field
    networkHidden : Int32
    networkInputWeight : StreamW
    networkCandidateWeight : StreamW
    networkGateWeight : StreamW
    networkActionHeads : NonEmptyActionHeads
open NetworkState public

record NetworkOutput : Set where
  constructor MkNetworkOutput
  field
    outputState : NetworkState
    outputAction : Nat
    outputPolicy : List Int32
    outputActionValues : List Int32
open NetworkOutput public

record NetworkTrainingResult : Set where
  constructor MkTrainingResult
  field
    trainedState : NetworkState
    trainedAction : Nat
    trainedTarget : Int32
    trainedTDError : Int32
open NetworkTrainingResult public

pairedActionHeads : List (Int32 × Int32) -> List ActionHead
pairedActionHeads [] = []
pairedActionHeads ((actorWeight , criticWeight) ∷ rest) =
  MkActionHead (MkSW actorWeight 0) (MkSW criticWeight 0)
    ∷ pairedActionHeads rest

networkInitialState :
  Int32 -> Int32 -> Int32 -> Int32 -> Int32 ->
  List (Int32 × Int32) -> NetworkState
networkInitialState inputWeight candidateWeight gateWeight
    firstActorWeight firstCriticWeight remainingWeights =
  MkNetworkState
    0
    (MkSW inputWeight 0)
    (MkSW candidateWeight 0)
    (MkSW gateWeight 0)
    (MkActionHeads
      (MkActionHead (MkSW firstActorWeight 0) (MkSW firstCriticWeight 0))
      (pairedActionHeads remainingWeights))

networkStep : Int32 -> Int32 -> NetworkState -> NetworkOutput
networkStep observation draw state =
  let cache =
        cellForward observation (networkHidden state)
          (streamWeight (networkInputWeight state))
          (streamWeight (networkCandidateWeight state))
          (streamWeight (networkGateWeight state))
      hidden = cellHiddenAfter cache
      logits = mapList (λ weight -> qMul weight hidden)
                  (streamValues (actionActorWeights (networkActionHeads state)))
      probabilities = policyProbabilities logits
      actionValues = mapList (λ weight -> qMul weight hidden)
                       (streamValues (actionCriticWeights (networkActionHeads state)))
      action = sampleAction draw probabilities
      nextState =
        MkNetworkState
          hidden
          (networkInputWeight state)
          (networkCandidateWeight state)
          (networkGateWeight state)
          (networkActionHeads state)
  in MkNetworkOutput nextState action probabilities actionValues

------------------------------------------------------------------------
-- On-policy one-step SARSA actor-critic update
------------------------------------------------------------------------

networkTrainStepSARSA :
  Int32 -> Int32 -> Int32 -> Int32 -> Int32 -> Bool -> Int32 ->
  NetworkState -> NetworkTrainingResult
networkTrainStepSARSA observation currentDraw reward nextObservation nextDraw terminal learningRate state =
  let current = networkStep observation currentDraw state
      next = networkStep nextObservation nextDraw (outputState current)
      action = outputAction current
      nextAction = outputAction next
      qCurrent = nthQ action (outputActionValues current)
      qNext = nthQ nextAction (outputActionValues next)
      target = qSarsaOneStepTarget reward qNext terminal
      td = qSub target qCurrent

      hiddenCurrent = networkHidden (outputState current)
      actorLogits =
        mapList (λ weight -> qMul weight hiddenCurrent)
          (streamValues (actionActorWeights (networkActionHeads state)))
      actorPreferences = mapList qPreference actorLogits
      preferenceTotal = sumQ64 actorPreferences
      actorScores = policyScoreFactors action preferenceTotal actorLogits actorPreferences
      actorDeltas = mapList (qMul td) actorScores
      actorHiddenSlope =
        sumQ (zipWithList qMul
          (streamValues (actionActorWeights (networkActionHeads state))) actorScores)
      criticCurrentWeight =
        streamWeight (actionCriticWeight (nthActionHead action (networkActionHeads state)))
      hiddenCotangent =
        qAdd (qMul td criticCurrentWeight) (qMul td actorHiddenSlope)

      cache =
        cellForward observation (networkHidden state)
          (streamWeight (networkInputWeight state))
          (streamWeight (networkCandidateWeight state))
          (streamWeight (networkGateWeight state))
      pullback =
        cellPullback
          (streamWeight (networkInputWeight state))
          (streamWeight (networkCandidateWeight state))
          (streamWeight (networkGateWeight state))
          cache hiddenCotangent

      inputWeightNext =
        streamStep (networkInputWeight state)
          (cellInputWeightCotangent pullback) qOne learningRate
      candidateWeightNext =
        streamStep (networkCandidateWeight state)
          (cellCandidateWeightCotangent pullback) qOne learningRate
      gateWeightNext =
        streamStep (networkGateWeight state)
          (cellGateWeightCotangent pullback) qOne learningRate
      actionHeadsNext =
        updateAllActionHeads action actorDeltas td hiddenCurrent learningRate
          (networkActionHeads state)
      finalHidden =
        if terminal then 0 else networkHidden (outputState next)
      nextState =
        MkNetworkState
          finalHidden
          inputWeightNext
          candidateWeightNext
          gateWeightNext
          actionHeadsNext
  in MkTrainingResult nextState action target td

------------------------------------------------------------------------
-- Iterative CHAD-style reverse scan for the recurrent cell.
--
-- Each input pair contains an observation and its local cotangent with
-- respect to the new hidden state. Forward consing stores frames newest
-- first. The reverse pass threads the future hidden cotangent and widened
-- Int64 parameter accumulators. Cotangents are for the smooth shadow of
-- Q8.24 operations, not derivatives of integer rounding itself.
------------------------------------------------------------------------

data CHADFrame : Set where
  MkCHADFrame : CellCache -> Int32 -> CHADFrame

record CHADGradient : Set where
  constructor MkCHADGradient
  field
    initialHiddenCotangent : Int32
    sequenceInputCotangents : List Int32
    inputWeightGradient64 : Int64
    candidateWeightGradient64 : Int64
    gateWeightGradient64 : Int64
open CHADGradient public

record CHADResult : Set where
  constructor MkCHADResult
  field
    chadFinalHidden : Int32
    chadGradient : CHADGradient
open CHADResult public

chadForward :
  List (Int32 × Int32) -> Int32 -> Int32 -> Int32 -> Int32 ->
  (Int32 × List CHADFrame)
chadForward frames hidden inputWeight candidateWeight gateWeight =
  go frames hidden []
  where
    go : List (Int32 × Int32) -> Int32 -> List CHADFrame ->
         (Int32 × List CHADFrame)
    go [] current reverseFrames = (current , reverseFrames)
    go ((observation , localCotangent) ∷ rest) current reverseFrames =
      let cache = cellForward observation current inputWeight candidateWeight gateWeight
      in go rest (cellHiddenAfter cache)
           (MkCHADFrame cache localCotangent ∷ reverseFrames)

chadBackward :
  Int32 -> Int32 -> Int32 -> List CHADFrame -> Int32 -> CHADGradient
chadBackward inputWeight candidateWeight gateWeight frames finalCotangent =
  go frames finalCotangent [] 0 0 0
  where
    go :
      List CHADFrame -> Int32 -> List Int32 ->
      Int64 -> Int64 -> Int64 -> CHADGradient
    go [] future inputCotangents inputAcc candidateAcc gateAcc =
      MkCHADGradient future inputCotangents inputAcc candidateAcc gateAcc
    go (MkCHADFrame cache localCotangent ∷ rest)
        future inputCotangents inputAcc candidateAcc gateAcc =
      let totalCotangent = qAdd future localCotangent
          pullback =
            cellPullback inputWeight candidateWeight gateWeight cache totalCotangent
      in go rest
           (cellHiddenCotangent pullback)
           (cellInputCotangent pullback ∷ inputCotangents)
           (inputAcc + fromIntegral (cellInputWeightCotangent pullback))
           (candidateAcc + fromIntegral (cellCandidateWeightCotangent pullback))
           (gateAcc + fromIntegral (cellGateWeightCotangent pullback))

iterativeCHAD :
  List (Int32 × Int32) -> Int32 -> Int32 -> Int32 -> Int32 -> Int32 ->
  CHADResult
iterativeCHAD frames initialHidden inputWeight candidateWeight gateWeight finalCotangent =
  let (finalHidden , reverseFrames) =
        chadForward frames initialHidden inputWeight candidateWeight gateWeight
      gradient =
        chadBackward inputWeight candidateWeight gateWeight reverseFrames finalCotangent
  in MkCHADResult finalHidden gradient

-- The caller supplies one local hidden-state cotangent per time step,
-- normally obtained from the categorical actor and scalar SARSA critic loss.
networkSequenceVJP :
  List (Int32 × Int32) -> Int32 -> NetworkState -> CHADResult
networkSequenceVJP frames finalCotangent state =
  iterativeCHAD
    frames
    (networkHidden state)
    (streamWeight (networkInputWeight state))
    (streamWeight (networkCandidateWeight state))
    (streamWeight (networkGateWeight state))
    finalCotangent

networkApplySequenceGradient :
  Int32 -> NetworkState -> CHADGradient -> NetworkState
networkApplySequenceGradient learningRate state gradient =
  MkNetworkState
    (networkHidden state)
    (streamStep (networkInputWeight state)
      (qFrom64 (inputWeightGradient64 gradient)) qOne learningRate)
    (streamStep (networkCandidateWeight state)
      (qFrom64 (candidateWeightGradient64 gradient)) qOne learningRate)
    (streamStep (networkGateWeight state)
      (qFrom64 (gateWeightGradient64 gradient)) qOne learningRate)
    (networkActionHeads state)

------------------------------------------------------------------------
-- Small executable checks for Q8.24 scaling and SARSA terminal behavior
------------------------------------------------------------------------

q24OneTimesOne : Bool
q24OneTimesOne = qMul qOne qOne == qOne

q24HalfTimesHalf : Bool
q24HalfTimesHalf = qMul qHalf qHalf == 4194304

sarsaTerminalDoesNotBootstrap : Bool
sarsaTerminalDoesNotBootstrap =
  qSarsaOneStepTarget 123456 987654 true == 123456

{-# COMPILE AGDA2HS qShift #-}
{-# COMPILE AGDA2HS qOne #-}
{-# COMPILE AGDA2HS qHalf #-}
{-# COMPILE AGDA2HS qQuarter #-}
{-# COMPILE AGDA2HS qTwo #-}
{-# COMPILE AGDA2HS qBeta #-}
{-# COMPILE AGDA2HS qEpsilon #-}
{-# COMPILE AGDA2HS qGamma #-}
{-# COMPILE AGDA2HS qFrom64 #-}
{-# COMPILE AGDA2HS qAdd #-}
{-# COMPILE AGDA2HS qSub #-}
{-# COMPILE AGDA2HS qNeg #-}
{-# COMPILE AGDA2HS qClamp #-}
{-# COMPILE AGDA2HS qAbs #-}
{-# COMPILE AGDA2HS qMul #-}
{-# COMPILE AGDA2HS qDiv64 #-}
{-# COMPILE AGDA2HS qDiv #-}
{-# COMPILE AGDA2HS qSoftsignGrad #-}
{-# COMPILE AGDA2HS qSoftsign #-}
{-# COMPILE AGDA2HS qRelu #-}
{-# COMPILE AGDA2HS qHardSigmoid #-}
{-# COMPILE AGDA2HS qHardSigmoidGrad #-}
{-# COMPILE AGDA2HS qSarsaOneStepTarget #-}
{-# COMPILE AGDA2HS StreamW #-}
{-# COMPILE AGDA2HS streamStep #-}
{-# COMPILE AGDA2HS CellCache #-}
{-# COMPILE AGDA2HS cellForward #-}
{-# COMPILE AGDA2HS CellPullback #-}
{-# COMPILE AGDA2HS cellPullback #-}
{-# COMPILE AGDA2HS mapList #-}
{-# COMPILE AGDA2HS zipWithList #-}
{-# COMPILE AGDA2HS sumQ #-}
{-# COMPILE AGDA2HS sumQ64 #-}
{-# COMPILE AGDA2HS nthQ #-}
{-# COMPILE AGDA2HS natEqual #-}
{-# COMPILE AGDA2HS streamValues #-}
{-# COMPILE AGDA2HS streamFromValues #-}
{-# COMPILE AGDA2HS qPreference #-}
{-# COMPILE AGDA2HS policyProbabilities #-}
{-# COMPILE AGDA2HS sampleAction #-}
{-# COMPILE AGDA2HS policyScoreFactors #-}
{-# COMPILE AGDA2HS ActionHead #-}
{-# COMPILE AGDA2HS NonEmptyActionHeads #-}
{-# COMPILE AGDA2HS actionActorWeights #-}
{-# COMPILE AGDA2HS actionCriticWeights #-}
{-# COMPILE AGDA2HS nthActionHead #-}
{-# COMPILE AGDA2HS pairedActionHeads #-}
{-# COMPILE AGDA2HS dropOne #-}
{-# COMPILE AGDA2HS updateOneActionHead #-}
{-# COMPILE AGDA2HS updateRemainingActionHeads #-}
{-# COMPILE AGDA2HS updateAllActionHeads #-}
{-# COMPILE AGDA2HS NetworkState #-}
{-# COMPILE AGDA2HS NetworkOutput #-}
{-# COMPILE AGDA2HS NetworkTrainingResult #-}
{-# COMPILE AGDA2HS networkInitialState #-}
{-# COMPILE AGDA2HS networkStep #-}
{-# COMPILE AGDA2HS networkTrainStepSARSA #-}
{-# COMPILE AGDA2HS CHADFrame #-}
{-# COMPILE AGDA2HS CHADGradient #-}
{-# COMPILE AGDA2HS CHADResult #-}
{-# COMPILE AGDA2HS chadForward #-}
{-# COMPILE AGDA2HS chadBackward #-}
{-# COMPILE AGDA2HS iterativeCHAD #-}
{-# COMPILE AGDA2HS networkSequenceVJP #-}
{-# COMPILE AGDA2HS networkApplySequenceGradient #-}
{-# COMPILE AGDA2HS q24OneTimesOne #-}
{-# COMPILE AGDA2HS q24HalfTimesHalf #-}
{-# COMPILE AGDA2HS sarsaTerminalDoesNotBootstrap #-}
