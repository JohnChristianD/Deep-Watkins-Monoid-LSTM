{-# OPTIONS
--no-projection-like
--syntactic-equality=1
--exact-split
--auto-inline
--erasure
--no-fast-reduce
--no-eta-equality
--rewriting
--confluence-check
--erased-quotients
#-}

module FullCoupled.CanonicalLearnerMonolith where

------------------------------------------------------------------------
-- Q8.24 recurrent Double distributional SARSA(0).
--
-- Two live dueling IQN32 critics, factorized NoisyNet value/advantage
-- layers, a one-use pending action, one critic update per transition,
-- and a scalar recurrent feature unit. There is no actor or target copy.
------------------------------------------------------------------------

open import Haskell.Prelude public
open import Haskell.Data.Int public
open import Haskell.Data.Bits public
open import Agda.Builtin.Equality.Rewrite public

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

qOne qHalf qQuarter qTwo qFour : Int32
qOne     = 16777216
qHalf    = 8388608
qQuarter = 4194304
qTwo     = 33554432
qFour    = 67108864

q63 q126 q127 qPi qTwoPi : Int32
q63    = 1056964608
q126   = 2113929216
q127   = 2130706432
qPi    = 52707179
qTwoPi = 105414358

qMax64 qMin64 : Int64
qMax64 = 2147483647
qMin64 = -2147483648

qGamma : Int32
qGamma = 16609444

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
  if denominator == 0 then 0
  else
    qFrom64
      (quot (shiftL (fromIntegral numerator) qShift) denominator)

qDiv : Int32 -> Int32 -> Int32
qDiv numerator denominator =
  qDiv64 numerator (fromIntegral denominator)

------------------------------------------------------------------------
-- Quantmoid4: quantized forward map and independent smooth CHAD shadow.
-- The standard IQN cosine embedding remains cosine; Quantmoid4 is used
-- only for the tanh-like recurrent feature transform.
------------------------------------------------------------------------

qExpSmall : Int32 -> Int32
qExpSmall x = qAdd qOne (qMul x p1)
  where
    p1 : Int32
    p1 = qAdd qOne (qMul x p2)

    p2 : Int32
    p2 = qAdd qHalf (qMul x p3)

    p3 : Int32
    p3 = qAdd 2796203 (qMul x p4)

    p4 : Int32
    p4 = qAdd 699051 (qMul x p5)

    p5 : Int32
    p5 = qAdd 139810 (qMul x 23302)

qSquare : Int32 -> Int32
qSquare x = qMul x x

qExpReduce : Int32 -> Int32
qExpReduce x =
  let small = qExpSmall (qDiv64 x 16)
  in qSquare (qSquare (qSquare (qSquare small)))

-- IDBD constrains beta to [-8, 0], so this approximation is used only
-- on that declared interval.
qExp : Int32 -> Int32
qExp x = qExpReduce (qClamp x (qNeg 134217728) 0)

qSigmoid2 : Int32 -> Int32
qSigmoid2 x =
  let exponential = qExp (qNeg (qMul qTwo (qAbs x)))
      denominator = qAdd qOne exponential
  in if x < 0 then qDiv exponential denominator
     else qDiv qOne denominator

qQuantmoid4 : Int32 -> Int32
qQuantmoid4 x =
  if x == 0 then q63
  else
    let scaled = qClamp (qMul (qAbs x) q127) 0 q127
        v = qSub scaled q127
        squareQuarter = qFrom64
          (shiftR (fromIntegral v * fromIntegral v) 32)
    in if 0 < x then qSub q126 squareQuarter else squareQuarter

q4Tanh : Int32 -> Int32
q4Tanh x =
  qSub (qDiv (qQuantmoid4 (qMul x qHalf)) q63) qOne

-- Derivative of the smooth tanh shadow, tanh(x) ~= 2 sigmoid(2x)-1.
-- It is a surrogate for the integer forward function, not its derivative.
q4TanhGrad : Int32 -> Int32
q4TanhGrad x =
  let p = qSigmoid2 x
  in qMul qFour (qMul p (qSub qOne p))

qRelu : Int32 -> Int32
qRelu x = if 0 < x then x else 0

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
-- At lambda = 0, the Dutch trace is the current feature, e_t = x_t (not 0).
-- Historical accumulation disappears and the true-online correction
-- cancels algebraically, leaving the ordinary one-step SARSA semi-gradient.
------------------------------------------------------------------------

trueOnlineEligibilityTraceLambdaZero : Int32 -> Int32
trueOnlineEligibilityTraceLambdaZero currentFeature = currentFeature

trueOnlineSarsaLambdaZeroUpdate :
  Int32 -> Int32 -> Int32 -> Int32 -> Int32
trueOnlineSarsaLambdaZeroUpdate alpha tdError currentFeature weight =
  qAdd weight
    (qMul alpha
      (qMul tdError
        (trueOnlineEligibilityTraceLambdaZero currentFeature)))

------------------------------------------------------------------------
-- Fixed-size vectors. A 32-entry vector is the IQN32 sample/embedding
-- dimension; it cannot silently become a shorter or longer sample batch.
------------------------------------------------------------------------

infixr 5 _∷ᵥ_

data Vec (A : Set) : Nat -> Set where
  []ᵥ : Vec A zero
  _∷ᵥ_ : ∀ {n} -> A -> Vec A n -> Vec A (suc n)

mapVec : {A B : Set} {n : Nat} -> (A -> B) -> Vec A n -> Vec B n
mapVec f []ᵥ = []ᵥ
mapVec f (x ∷ᵥ xs) = f x ∷ᵥ mapVec f xs

zipVecWith :
  {A B C : Set} {n : Nat} ->
  (A -> B -> C) -> Vec A n -> Vec B n -> Vec C n
zipVecWith f []ᵥ []ᵥ = []ᵥ
zipVecWith f (x ∷ᵥ xs) (y ∷ᵥ ys) =
  f x y ∷ᵥ zipVecWith f xs ys

zipVecWith3 :
  {A B C D : Set} {n : Nat} ->
  (A -> B -> C -> D) ->
  Vec A n -> Vec B n -> Vec C n -> Vec D n
zipVecWith3 f []ᵥ []ᵥ []ᵥ = []ᵥ
zipVecWith3 f (x ∷ᵥ xs) (y ∷ᵥ ys) (z ∷ᵥ zs) =
  f x y z ∷ᵥ zipVecWith3 f xs ys zs

foldVec :
  {A B : Set} {n : Nat} ->
  (B -> A -> B) -> B -> Vec A n -> B
foldVec f initial []ᵥ = initial
foldVec f initial (x ∷ᵥ xs) =
  foldVec f (f initial x) xs

qSumVec : Vec Int32 n -> Int32
qSumVec = foldVec qAdd 0

qSumVec64 : Vec Int32 n -> Int64
qSumVec64 = foldVec (λ total value -> total + fromIntegral value) 0

qMean32 : Vec Int32 32 -> Int32
qMean32 values =
  qFrom64 (quot (qSumVec64 values) 32)

qNat : Nat -> Int32
qNat value = qFrom64 (fromIntegral value * fromIntegral qOne)

indices32 : Vec Nat 32
indices32 =
  0 ∷ᵥ 1 ∷ᵥ 2 ∷ᵥ 3 ∷ᵥ 4 ∷ᵥ 5 ∷ᵥ 6 ∷ᵥ 7 ∷ᵥ
  8 ∷ᵥ 9 ∷ᵥ 10 ∷ᵥ 11 ∷ᵥ 12 ∷ᵥ 13 ∷ᵥ 14 ∷ᵥ 15 ∷ᵥ
  16 ∷ᵥ 17 ∷ᵥ 18 ∷ᵥ 19 ∷ᵥ 20 ∷ᵥ 21 ∷ᵥ 22 ∷ᵥ 23 ∷ᵥ
  24 ∷ᵥ 25 ∷ᵥ 26 ∷ᵥ 27 ∷ᵥ 28 ∷ᵥ 29 ∷ᵥ 30 ∷ᵥ 31 ∷ᵥ []ᵥ

-- Range-reduce to [-pi, pi], then evaluate a Q8.24 cosine polynomial.
-- This preserves the periodic IQN basis instead of substituting tanh.
qCos : Int32 -> Int32
qCos angle =
  let turns =
        quot
          (fromIntegral (qAdd angle qPi))
          (fromIntegral qTwoPi)
      reduced =
        qSub angle (qFrom64 (turns * fromIntegral qTwoPi))
      x2 = qMul reduced reduced
      polynomial =
        qAdd (-8388608)
          (qMul x2
            (qAdd 699051
              (qMul x2
                (qAdd (-23302)
                  (qMul x2
                    (qAdd 416
                      (qMul x2 (-5))))))))
  in qAdd qOne (qMul x2 polynomial)

record IQNQuantile : Set where
  constructor MkIQNQuantile
  field
    quantileFraction : Int32
    cosineEmbedding : Vec Int32 32
open IQNQuantile public

makeIQNQuantile : Int32 -> IQNQuantile
makeIQNQuantile tau =
  MkIQNQuantile tau
    (mapVec
      (λ index -> qCos (qMul (qMul qPi (qNat index)) tau))
      indices32)

makeIQNBatch32 : Vec Int32 32 -> Vec IQNQuantile 32
makeIQNBatch32 = mapVec makeIQNQuantile

------------------------------------------------------------------------
-- Euclidean Q-projected diagonal IDBD. The projection is the coordinatewise
-- Euclidean projection onto the declared closed box [-8, 0].
-- L2 enters the gradient before the parameter update. There is no global
-- norm clipping, max-gradient normalization, or fixed weight shrink.
------------------------------------------------------------------------

record IDBDConfig : Set where
  constructor MkIDBDConfig
  field
    idbdMetaRate : Int32
    l2GradientDecay : Int32
open IDBDConfig public

record IDBDParameter : Set where
  constructor MkIDBDParameter
  field
    idbdWeight : Int32
    idbdLogStepSize : Int32
    idbdSensitivity : Int32
    idbdDiagonalCurvature : Int32
open IDBDParameter public

idbdBetaMin idbdBetaMax : Int32
idbdBetaMin = -134217728
idbdBetaMax = 0

idbdInitial : Int32 -> IDBDParameter
idbdInitial weight = MkIDBDParameter weight (-125829120) 0 0

idbdStep :
  IDBDConfig -> Int32 -> IDBDParameter -> IDBDParameter
idbdStep config dataGradient parameter =
  let weight = idbdWeight parameter
      regularizedGradient =
        qAdd dataGradient (qMul (l2GradientDecay config) weight)
      beta = qClamp (idbdLogStepSize parameter) idbdBetaMin idbdBetaMax
      alpha = qExp beta
      sensitivity = idbdSensitivity parameter
      curvature = idbdDiagonalCurvature parameter
      nextWeight = qSub weight (qMul alpha regularizedGradient)
      nextSensitivity =
        qSub sensitivity
          (qMul alpha
            (qAdd regularizedGradient (qMul curvature sensitivity)))
      metaDirection =
        qMul (idbdMetaRate config)
          (qMul regularizedGradient sensitivity)
      nextBeta =
        qClamp (qSub beta metaDirection) idbdBetaMin idbdBetaMax
  in MkIDBDParameter nextWeight nextBeta nextSensitivity curvature

record NoisyParameter : Set where
  constructor MkNoisyParameter
  field
    noisyMean : IDBDParameter
    noisyScale : IDBDParameter
open NoisyParameter public

record NoisyDense32 : Set where
  constructor MkNoisyDense32
  field
    denseWeights : Vec NoisyParameter 32
    denseBias : NoisyParameter
open NoisyDense32 public

record NoisyDenseNoise32 : Set where
  constructor MkNoisyDenseNoise32
  field
    -- Already transformed factorized noise f(epsilon)=sgn(epsilon)*sqrt(|epsilon|).
    denseInputNoise : Vec Int32 32
    denseOutputNoise : Int32
open NoisyDenseNoise32 public

effectiveNoisyParameter : NoisyParameter -> Int32 -> Int32 -> Int32
effectiveNoisyParameter parameter inputNoise outputNoise =
  qAdd (idbdWeight (noisyMean parameter))
    (qMul (idbdWeight (noisyScale parameter))
      (qMul inputNoise outputNoise))

effectiveDenseWeights :
  NoisyDense32 -> NoisyDenseNoise32 -> Vec Int32 32
effectiveDenseWeights dense noise =
  zipVecWith3
    (λ parameter inputNoise outputNoise ->
      effectiveNoisyParameter parameter inputNoise outputNoise)
    (denseWeights dense)
    (denseInputNoise noise)
    (mapVec (λ _ -> denseOutputNoise noise) indices32)

noisyDenseForward :
  NoisyDense32 -> NoisyDenseNoise32 -> Vec Int32 32 -> Int32
noisyDenseForward dense noise features =
  qAdd
    (qSumVec (zipVecWith qMul
      (effectiveDenseWeights dense noise) features))
    (effectiveNoisyParameter
      (denseBias dense) qOne (denseOutputNoise noise))

record NonEmptyNoisyDense : Set where
  constructor MkNonEmptyNoisyDense
  field
    firstNoisyDense : NoisyDense32
    remainingNoisyDense : List NoisyDense32
open NonEmptyNoisyDense public

record NonEmptyNoisyDenseNoise : Set where
  constructor MkNonEmptyNoisyDenseNoise
  field
    firstDenseNoise : NoisyDenseNoise32
    remainingDenseNoise : List NoisyDenseNoise32
open NonEmptyNoisyDenseNoise public

record DuelingIQN32 : Set where
  constructor MkDuelingIQN32
  field
    duelingValue : NoisyDense32
    duelingAdvantages : NonEmptyNoisyDense
open DuelingIQN32 public

record DuelingIQN32Noise : Set where
  constructor MkDuelingIQN32Noise
  field
    duelingValueNoise : NoisyDenseNoise32
    duelingAdvantageNoise : NonEmptyNoisyDenseNoise
open DuelingIQN32Noise public

denseOutputs :
  NonEmptyNoisyDense -> NonEmptyNoisyDenseNoise ->
  Vec Int32 32 -> List Int32
denseOutputs
  (MkNonEmptyNoisyDense first rest)
  (MkNonEmptyNoisyDenseNoise firstNoise restNoise)
  features =
  noisyDenseForward first firstNoise features
    ∷ denseOutputsRest rest restNoise features
  where
    denseOutputsRest :
      List NoisyDense32 -> List NoisyDenseNoise32 ->
      Vec Int32 32 -> List Int32
    denseOutputsRest [] [] features = []
    denseOutputsRest (head ∷ heads) (noise ∷ noises) features =
      noisyDenseForward head noise features
        ∷ denseOutputsRest heads noises features
    denseOutputsRest [] (noise ∷ noises) features = []
    denseOutputsRest (head ∷ heads) [] features = []

nthQ : Nat -> List Int32 -> Int32
nthQ zero (value ∷ values) = value
nthQ (suc index) (value ∷ values) = nthQ index values
nthQ index [] = 0

listCount : {A : Set} -> List A -> Nat
listCount [] = zero
listCount (value ∷ values) = suc (listCount values)

listSum64 : List Int32 -> Int64
listSum64 [] = 0
listSum64 (value ∷ values) =
  fromIntegral value + listSum64 values

qMeanList : List Int32 -> Int32
qMeanList [] = 0
qMeanList values =
  qFrom64 (quot (listSum64 values) (fromIntegral (listCount values)))

qQuantileFeatures : Int32 -> IQNQuantile -> Vec Int32 32
qQuantileFeatures hidden quantile =
  mapVec (qMul hidden) (cosineEmbedding quantile)

criticQuantileForAction :
  Nat -> DuelingIQN32 -> DuelingIQN32Noise ->
  Int32 -> IQNQuantile -> Int32
criticQuantileForAction action critic noise hidden quantile =
  let features = qQuantileFeatures hidden quantile
      value =
        noisyDenseForward
          (duelingValue critic)
          (duelingValueNoise noise)
          features
      advantages =
        denseOutputs
          (duelingAdvantages critic)
          (duelingAdvantageNoise noise)
          features
      chosen = nthQ action advantages
      centered = qSub chosen (qMeanList advantages)
  in qAdd value centered

criticQuantilesForAction :
  Nat -> DuelingIQN32 -> DuelingIQN32Noise -> Int32 ->
  Vec IQNQuantile 32 -> Vec Int32 32
criticQuantilesForAction action critic noise hidden =
  mapVec (criticQuantileForAction action critic noise hidden)

actionMeansGo :
  Nat -> List NoisyDense32 -> DuelingIQN32 -> DuelingIQN32Noise ->
  Int32 -> Vec IQNQuantile 32 -> List Int32
actionMeansGo index [] critic noise hidden quantiles = []
actionMeansGo index (head ∷ rest) critic noise hidden quantiles =
  qMean32 (criticQuantilesForAction index critic noise hidden quantiles)
    ∷ actionMeansGo (suc index) rest critic noise hidden quantiles

criticActionMeans :
  DuelingIQN32 -> DuelingIQN32Noise -> Int32 ->
  Vec IQNQuantile 32 -> List Int32
criticActionMeans critic noise hidden quantiles =
  actionMeansGo zero
    (firstNoisyDense (duelingAdvantages critic)
      ∷ remainingNoisyDense (duelingAdvantages critic))
    critic noise hidden quantiles

argmaxGo : Nat -> Nat -> Int32 -> List Int32 -> Nat
argmaxGo index bestIndex bestValue [] = bestIndex
argmaxGo index bestIndex bestValue (value ∷ values) =
  if bestValue < value
  then argmaxGo (suc index) index value values
  else argmaxGo (suc index) bestIndex bestValue values

argmaxList : List Int32 -> Nat
argmaxList [] = 0
argmaxList (first ∷ rest) = argmaxGo (suc zero) zero first rest

criticSelectAction :
  DuelingIQN32 -> DuelingIQN32Noise -> Int32 ->
  Vec IQNQuantile 32 -> Nat
criticSelectAction critic noise hidden quantiles =
  argmaxList (criticActionMeans critic noise hidden quantiles)

------------------------------------------------------------------------
-- Double distributional SARSA(0): one noisy active critic selects one action;
-- the other live critic evaluates that exact action. Both critics are current
-- trainable parameter sets. No target copy, actor, replay, or multi-step return.
------------------------------------------------------------------------

record TwinDuelingCritics : Set where
  constructor MkTwinDuelingCritics
  field
    onlineCriticA : DuelingIQN32
    onlineCriticB : DuelingIQN32
    activeCriticA : Bool
open TwinDuelingCritics public

record TwinDuelingNoise : Set where
  constructor MkTwinDuelingNoise
  field
    noiseForCriticA : DuelingIQN32Noise
    noiseForCriticB : DuelingIQN32Noise
open TwinDuelingNoise public

record DoubleSARSA0Target : Set where
  constructor MkDoubleSARSA0Target
  field
    doubleSelectedAction : Nat
    doubleTargetQuantiles : Vec Int32 32
open DoubleSARSA0Target public

selectActiveCritic :
  Bool -> TwinDuelingCritics -> DuelingIQN32
selectActiveCritic true critics = onlineCriticA critics
selectActiveCritic false critics = onlineCriticB critics

selectPeerCritic :
  Bool -> TwinDuelingCritics -> DuelingIQN32
selectPeerCritic true critics = onlineCriticB critics
selectPeerCritic false critics = onlineCriticA critics

selectActiveNoise :
  Bool -> TwinDuelingNoise -> DuelingIQN32Noise
selectActiveNoise true noises = noiseForCriticA noises
selectActiveNoise false noises = noiseForCriticB noises

selectPeerNoise :
  Bool -> TwinDuelingNoise -> DuelingIQN32Noise
selectPeerNoise true noises = noiseForCriticB noises
selectPeerNoise false noises = noiseForCriticA noises

flipBool : Bool -> Bool
flipBool true = false
flipBool false = true

doubleSARSA0Target :
  TwinDuelingCritics -> TwinDuelingNoise -> Int32 ->
  Vec IQNQuantile 32 -> Vec IQNQuantile 32 -> Int32 -> Bool ->
  DoubleSARSA0Target
doubleSARSA0Target critics noises hidden actionQuantiles targetQuantiles
    reward terminal =
  let active = selectActiveCritic (activeCriticA critics) critics
      peer = selectPeerCritic (activeCriticA critics) critics
      activeNoise = selectActiveNoise (activeCriticA critics) noises
      peerNoise = selectPeerNoise (activeCriticA critics) noises
      action =
        criticSelectAction active activeNoise hidden actionQuantiles
      peerValues =
        criticQuantilesForAction action peer peerNoise hidden targetQuantiles
      targets =
        if terminal
        then mapVec (λ _ -> reward) targetQuantiles
        else mapVec (λ value -> qSarsaOneStepTarget reward value false)
                    peerValues
  in MkDoubleSARSA0Target action targets

------------------------------------------------------------------------
-- Quantile-Huber objective and its derivative with respect to each current
-- quantile. Each pair contributes 1/(32*32); target values are constants.
------------------------------------------------------------------------

qHuber : Int32 -> Int32
qHuber residual =
  let magnitude = qAbs residual
  in if magnitude <= qOne
     then qMul qHalf (qMul residual residual)
     else qSub magnitude qHalf

qQuantileWeight : Int32 -> Int32 -> Int32
qQuantileWeight tau residual =
  let indicator = if residual < 0 then qOne else 0
  in qAbs (qSub tau indicator)

qQuantileHuberPair : Int32 -> Int32 -> Int32 -> Int32
qQuantileHuberPair tau target prediction =
  let residual = qSub target prediction
      weighted = qMul (qQuantileWeight tau residual) (qHuber residual)
  in qFrom64 (shiftR (fromIntegral weighted) 10)

qQuantileHuberPairGradient : Int32 -> Int32 -> Int32 -> Int32
qQuantileHuberPairGradient tau target prediction =
  let residual = qSub target prediction
      bounded = qClamp residual (qNeg qOne) qOne
      weighted = qNeg (qMul (qQuantileWeight tau residual) bounded)
  in qFrom64 (shiftR (fromIntegral weighted) 10)

qQuantileLossForCurrent :
  IQNQuantile -> Int32 -> Vec Int32 32 -> Int32
qQuantileLossForCurrent quantile prediction targets =
  foldVec
    (λ total target ->
      qAdd total
        (qQuantileHuberPair
          (quantileFraction quantile) target prediction))
    0 targets

qQuantileGradientForCurrent :
  IQNQuantile -> Int32 -> Vec Int32 32 -> Int32
qQuantileGradientForCurrent quantile prediction targets =
  foldVec
    (λ total target ->
      qAdd total
        (qQuantileHuberPairGradient
          (quantileFraction quantile) target prediction))
    0 targets

quantileHuberLoss32 :
  Vec IQNQuantile 32 -> Vec Int32 32 -> Vec Int32 32 -> Int32
quantileHuberLoss32 quantiles predictions targets =
  qSumVec
    (zipVecWith
      (λ quantile prediction ->
        qQuantileLossForCurrent quantile prediction targets)
      quantiles predictions)

quantileHuberGradients32 :
  Vec IQNQuantile 32 -> Vec Int32 32 -> Vec Int32 32 -> Vec Int32 32
quantileHuberGradients32 quantiles predictions targets =
  zipVecWith
    (λ quantile prediction ->
      qQuantileGradientForCurrent quantile prediction targets)
    quantiles predictions

------------------------------------------------------------------------
-- IDBD gradient accumulation for a noisy 32-input affine layer.
------------------------------------------------------------------------

record DenseSample32 : Set where
  constructor MkDenseSample32
  field
    denseSampleFeatures : Vec Int32 32
    denseSampleGradient : Int32
open DenseSample32 public

record DenseGradient32 : Set where
  constructor MkDenseGradient32
  field
    denseMeanGradient : Vec Int32 32
    denseScaleGradient : Vec Int32 32
    denseBiasMeanGradient : Int32
    denseBiasScaleGradient : Int32
open DenseGradient32 public

zeroDenseGradient32 : DenseGradient32
zeroDenseGradient32 =
  MkDenseGradient32
    (mapVec (λ _ -> 0) indices32)
    (mapVec (λ _ -> 0) indices32)
    0 0

denseGradientAccumulate :
  NoisyDenseNoise32 -> DenseGradient32 -> DenseSample32 -> DenseGradient32
denseGradientAccumulate noise accumulated sample =
  let outputGradient = denseSampleGradient sample
      meanDelta =
        mapVec (qMul outputGradient) (denseSampleFeatures sample)
      scaleDelta =
        zipVecWith3
          (λ gradient feature inputNoise ->
            qMul
              (qMul (qMul gradient feature) inputNoise)
              (denseOutputNoise noise))
          (mapVec (λ _ -> outputGradient) indices32)
          (denseSampleFeatures sample)
          (denseInputNoise noise)
  in MkDenseGradient32
       (zipVecWith qAdd (denseMeanGradient accumulated) meanDelta)
       (zipVecWith qAdd (denseScaleGradient accumulated) scaleDelta)
       (qAdd (denseBiasMeanGradient accumulated) outputGradient)
       (qAdd (denseBiasScaleGradient accumulated)
         (qMul outputGradient (denseOutputNoise noise)))

denseGradientFromSamples :
  NoisyDenseNoise32 -> Vec DenseSample32 32 -> DenseGradient32
denseGradientFromSamples noise =
  foldVec (denseGradientAccumulate noise) zeroDenseGradient32

makeDenseSamples :
  Int32 -> Vec IQNQuantile 32 -> Vec Int32 32 -> Vec DenseSample32 32
makeDenseSamples hidden quantiles gradients =
  zipVecWith
    (λ quantile gradient ->
      MkDenseSample32 (qQuantileFeatures hidden quantile) gradient)
    quantiles gradients

updateNoisyParameter :
  IDBDConfig -> NoisyParameter -> Int32 -> Int32 -> NoisyParameter
updateNoisyParameter config parameter meanGradient scaleGradient =
  MkNoisyParameter
    (idbdStep config meanGradient (noisyMean parameter))
    (idbdStep config scaleGradient (noisyScale parameter))

updateNoisyDense :
  IDBDConfig -> NoisyDense32 -> NoisyDenseNoise32 ->
  DenseGradient32 -> NoisyDense32
updateNoisyDense config dense noise gradient =
  MkNoisyDense32
    (zipVecWith3
      (λ parameter meanGradient scaleGradient ->
        updateNoisyParameter config parameter meanGradient scaleGradient)
      (denseWeights dense)
      (denseMeanGradient gradient)
      (denseScaleGradient gradient))
    (updateNoisyParameter config (denseBias dense)
      (denseBiasMeanGradient gradient)
      (denseBiasScaleGradient gradient))

denseGradientForBatch :
  NoisyDenseNoise32 -> Int32 -> Vec IQNQuantile 32 ->
  Vec Int32 32 -> DenseGradient32
denseGradientForBatch noise hidden quantiles gradients =
  denseGradientFromSamples noise
    (makeDenseSamples hidden quantiles gradients)

updateNoisyDenseForBatch :
  IDBDConfig -> NoisyDense32 -> NoisyDenseNoise32 ->
  Int32 -> Vec IQNQuantile 32 -> Vec Int32 32 -> NoisyDense32
updateNoisyDenseForBatch config dense noise hidden quantiles gradients =
  updateNoisyDense config dense noise
    (denseGradientForBatch noise hidden quantiles gradients)

scaleGradients : Int32 -> Vec Int32 32 -> Vec Int32 32
scaleGradients factor =
  mapVec (qMul factor)

updateAdvantageHeads :
  IDBDConfig -> Nat -> Nat -> Nat -> Int32 ->
  NonEmptyNoisyDense -> NonEmptyNoisyDenseNoise ->
  Int32 -> Vec IQNQuantile 32 -> Vec Int32 32 ->
  NonEmptyNoisyDense
updateAdvantageHeads config index selected count inverseCount
    (MkNonEmptyNoisyDense first rest)
    (MkNonEmptyNoisyDenseNoise firstNoise restNoise)
    hidden quantiles gradients =
  let coefficient =
        if natEqual index selected
        then qSub qOne inverseCount
        else qNeg inverseCount
      headGradient = scaleGradients coefficient gradients
      updatedFirst =
        updateNoisyDenseForBatch config first firstNoise hidden
          quantiles headGradient
  in MkNonEmptyNoisyDense
       updatedFirst
       (updateAdvantageRest config (suc index) selected inverseCount
         rest restNoise hidden quantiles gradients)
  where
    updateAdvantageRest :
      IDBDConfig -> Nat -> Nat -> Int32 ->
      List NoisyDense32 -> List NoisyDenseNoise32 ->
      Int32 -> Vec IQNQuantile 32 -> Vec Int32 32 ->
      List NoisyDense32
    updateAdvantageRest config index selected inverseCount [] [] hidden quantiles gradients = []
    updateAdvantageRest config index selected inverseCount
        (head ∷ rest) (noise ∷ noises) hidden quantiles gradients =
      let coefficient =
            if natEqual index selected
            then qSub qOne inverseCount
            else qNeg inverseCount
      in updateNoisyDenseForBatch config head noise hidden quantiles
           (scaleGradients coefficient gradients)
           ∷ updateAdvantageRest config (suc index) selected inverseCount
                rest noises hidden quantiles gradients
    updateAdvantageRest config index selected inverseCount [] (noise ∷ noises) hidden quantiles gradients = []
    updateAdvantageRest config index selected inverseCount (head ∷ rest) [] hidden quantiles gradients = []

criticUpdateFromQuantileGradients :
  IDBDConfig -> DuelingIQN32 -> DuelingIQN32Noise ->
  Nat -> Int32 -> Vec IQNQuantile 32 -> Vec Int32 32 ->
  DuelingIQN32
criticUpdateFromQuantileGradients config critic noise selected hidden
    quantiles gradients =
  let advantageLayers =
        firstNoisyDense (duelingAdvantages critic)
          ∷ remainingNoisyDense (duelingAdvantages critic)
      count = qNat (listCount advantageLayers)
      inverseCount = qDiv qOne count
      valueGradient =
        denseGradientForBatch (duelingValueNoise noise)
          hidden quantiles gradients
      updatedValue =
        updateNoisyDense config (duelingValue critic)
          (duelingValueNoise noise) valueGradient
      updatedAdvantages =
        updateAdvantageHeads config zero selected
          (listCount advantageLayers) inverseCount
          (duelingAdvantages critic) (duelingAdvantageNoise noise)
          hidden quantiles gradients
  in MkDuelingIQN32 updatedValue updatedAdvantages

denseSlope :
  NoisyDense32 -> NoisyDenseNoise32 -> Vec Int32 32 -> Int32
denseSlope dense noise cosine =
  qSumVec (zipVecWith qMul (effectiveDenseWeights dense noise) cosine)

criticHiddenSlope :
  DuelingIQN32 -> DuelingIQN32Noise -> Nat -> Vec Int32 32 -> Int32
criticHiddenSlope critic noise action cosine =
  let valueSlope =
        denseSlope (duelingValue critic) (duelingValueNoise noise) cosine
      actionSlopes =
        denseOutputs (duelingAdvantages critic)
          (duelingAdvantageNoise noise) cosine
      selectedSlope = nthQ action actionSlopes
      centeredSlope = qSub selectedSlope (qMeanList actionSlopes)
  in qAdd valueSlope centeredSlope

criticHiddenCotangent :
  DuelingIQN32 -> DuelingIQN32Noise -> Nat -> Int32 ->
  Vec IQNQuantile 32 -> Vec Int32 32 -> Int32
criticHiddenCotangent critic noise action hidden quantiles gradients =
  qSumVec
    (zipVecWith
      (λ quantile gradient ->
        qMul gradient
          (criticHiddenSlope critic noise action
            (cosineEmbedding quantile)))
      quantiles gradients)

------------------------------------------------------------------------
-- Recurrent scalar feature unit. Quantmoid4's integer forward path is paired
-- with its explicit smooth-shadow derivative for the local VJP and CHAD scan.
------------------------------------------------------------------------

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

cellForward :
  Int32 -> Int32 -> Int32 -> Int32 -> Int32 -> CellCache
cellForward raw hidden inputWeight candidateWeight gateWeight =
  let preFeature = qMul inputWeight raw
      feature = q4Tanh preFeature
      gateInput = qAdd feature (qMul gateWeight hidden)
      gate = qHardSigmoid gateInput
      candidateInput = qAdd feature (qMul candidateWeight hidden)
      candidate = qRelu candidateInput
      mixPre =
        qAdd
          (qMul (qSub qOne gate) hidden)
          (qMul gate candidate)
      hiddenAfter = qRelu mixPre
  in MkCellCache raw hidden preFeature feature gateInput gate
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

cellPullback :
  Int32 -> Int32 -> Int32 -> CellCache -> Int32 -> CellPullback
cellPullback inputWeight candidateWeight gateWeight cache hiddenCotangent =
  let gate = cellGate cache
      hidden = cellHiddenBefore cache
      candidate = cellCandidate cache
      mixCotangent =
        if 0 < cellMixPre cache then hiddenCotangent else 0
      candidateCotangent = qMul mixCotangent gate
      candidateInputCotangent =
        if 0 < cellCandidateInput cache then candidateCotangent else 0
      gateCotangent = qMul mixCotangent (qSub candidate hidden)
      gateInputCotangent =
        qMul gateCotangent (qHardSigmoidGrad (cellGateInput cache))
      featureCotangent = qAdd candidateInputCotangent gateInputCotangent
      preFeatureCotangent =
        qMul featureCotangent (q4TanhGrad (cellPreFeature cache))
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
  in MkCellPullback hiddenCotangentBefore inputCotangent
       inputWeightCotangent candidateWeightCotangent gateWeightCotangent

------------------------------------------------------------------------
-- Pending-decision boundary and transition-alternating Double SARSA policy.
-- The active critic alternates A/B after every transition. The selected next
-- action is carried unchanged; the peer evaluates that exact action.
------------------------------------------------------------------------

record NetworkState : Set where
  constructor MkNetworkState
  field
    networkInputParameter : IDBDParameter
    networkCandidateParameter : IDBDParameter
    networkGateParameter : IDBDParameter
    networkCritics : TwinDuelingCritics
open NetworkState public

record PendingDecision : Set where
  constructor MkPendingDecision
  field
    pendingAction : Nat
    pendingCellCache : CellCache
    pendingCurrentQuantiles : Vec IQNQuantile 32
    pendingCriticNoise : DuelingIQN32Noise
open PendingDecision public

data TransitionOutput : Set where
  EpisodeEnded : TransitionOutput
  ContinueWith : PendingDecision -> TransitionOutput

record NetworkTrainingResult : Set where
  constructor MkNetworkTrainingResult
  field
    resultNetworkState : NetworkState
    resultTargets : Vec Int32 32
    resultQuantileLoss : Int32
    resultSelectedNextAction : Nat
    resultTransitionOutput : TransitionOutput
open NetworkTrainingResult public

record NetworkStartResult : Set where
  constructor MkNetworkStartResult
  field
    startedNetworkState : NetworkState
    startedPendingDecision : PendingDecision
open NetworkStartResult public

networkInitialState :
  Int32 -> Int32 -> Int32 -> DuelingIQN32 -> DuelingIQN32 ->
  Bool -> NetworkState
networkInitialState inputWeight candidateWeight gateWeight
    criticA criticB activeA =
  MkNetworkState
    (idbdInitial inputWeight)
    (idbdInitial candidateWeight)
    (idbdInitial gateWeight)
    (MkTwinDuelingCritics criticA criticB activeA)

networkStart :
  Int32 -> Vec Int32 32 -> Vec Int32 32 ->
  DuelingIQN32Noise -> NetworkState -> NetworkStartResult
networkStart observation actionFractions currentFractions
    activeNoise state =
  let cache =
        cellForward observation 0
          (idbdWeight (networkInputParameter state))
          (idbdWeight (networkCandidateParameter state))
          (idbdWeight (networkGateParameter state))
      hidden = cellHiddenAfter cache
      activeA = activeCriticA (networkCritics state)
      active = selectActiveCritic activeA (networkCritics state)
      actionBatch = makeIQNBatch32 actionFractions
      currentBatch = makeIQNBatch32 currentFractions
      action =
        criticSelectAction active activeNoise hidden actionBatch
      nextCritics =
        MkTwinDuelingCritics
          (onlineCriticA (networkCritics state))
          (onlineCriticB (networkCritics state))
          activeA
      nextState =
        MkNetworkState
          (networkInputParameter state)
          (networkCandidateParameter state)
          (networkGateParameter state)
          nextCritics
      pending =
        MkPendingDecision action cache currentBatch activeNoise
  in MkNetworkStartResult nextState pending

makeTargetsForAction :
  Bool -> Int32 -> Nat -> DuelingIQN32 -> DuelingIQN32Noise -> Int32 ->
  Vec IQNQuantile 32 -> Vec Int32 32
makeTargetsForAction terminal reward action peer peerNoise hidden targetBatch =
  if terminal
  then mapVec (λ _ -> reward) targetBatch
  else
    mapVec
      (λ value -> qSarsaOneStepTarget reward value false)
      (criticQuantilesForAction action peer peerNoise hidden targetBatch)

networkTrainStepSARSA0 :
  IDBDConfig -> NetworkState -> PendingDecision ->
  Int32 -> Int32 -> Bool ->
  Vec Int32 32 -> Vec Int32 32 -> Vec Int32 32 ->
  DuelingIQN32Noise -> DuelingIQN32Noise -> NetworkTrainingResult
networkTrainStepSARSA0 config state pending reward nextObservation terminal
    nextActionFractions nextCurrentFractions nextTargetFractions
    activeNextNoise peerNextNoise =
  let critics = networkCritics state
      activeA = activeCriticA critics
      active = selectActiveCritic activeA critics
      peer = selectPeerCritic activeA critics
      currentHidden = cellHiddenAfter (pendingCellCache pending)
      currentPredictions =
        criticQuantilesForAction (pendingAction pending)
          active (pendingCriticNoise pending) currentHidden
          (pendingCurrentQuantiles pending)
      nextCache =
        cellForward nextObservation currentHidden
          (idbdWeight (networkInputParameter state))
          (idbdWeight (networkCandidateParameter state))
          (idbdWeight (networkGateParameter state))
      nextHidden = cellHiddenAfter nextCache
      nextActionBatch = makeIQNBatch32 nextActionFractions
      nextCurrentBatch = makeIQNBatch32 nextCurrentFractions
      nextTargetBatch = makeIQNBatch32 nextTargetFractions
      nextAction =
        if terminal then 0
        else criticSelectAction active activeNextNoise nextHidden nextActionBatch
      targets =
        makeTargetsForAction terminal reward nextAction peer peerNextNoise
          nextHidden nextTargetBatch
      quantileGradients =
        quantileHuberGradients32
          (pendingCurrentQuantiles pending) currentPredictions targets
      loss =
        quantileHuberLoss32
          (pendingCurrentQuantiles pending) currentPredictions targets
      updatedActive =
        criticUpdateFromQuantileGradients config active
          (pendingCriticNoise pending) (pendingAction pending)
          currentHidden (pendingCurrentQuantiles pending) quantileGradients
      hiddenCotangent =
        criticHiddenCotangent active (pendingCriticNoise pending)
          (pendingAction pending) currentHidden
          (pendingCurrentQuantiles pending) quantileGradients
      pullback =
        cellPullback
          (idbdWeight (networkInputParameter state))
          (idbdWeight (networkCandidateParameter state))
          (idbdWeight (networkGateParameter state))
          (pendingCellCache pending) hiddenCotangent
      nextInputParameter =
        idbdStep config (cellInputWeightCotangent pullback)
          (networkInputParameter state)
      nextCandidateParameter =
        idbdStep config (cellCandidateWeightCotangent pullback)
          (networkCandidateParameter state)
      nextGateParameter =
        idbdStep config (cellGateWeightCotangent pullback)
          (networkGateParameter state)
      nextActiveA = flipBool activeA
      nextCritics =
        if activeA
        then MkTwinDuelingCritics updatedActive (onlineCriticB critics) nextActiveA
        else MkTwinDuelingCritics (onlineCriticA critics) updatedActive nextActiveA
      nextState =
        MkNetworkState nextInputParameter nextCandidateParameter
          nextGateParameter nextCritics
      output =
        if terminal then EpisodeEnded
        else ContinueWith
          (MkPendingDecision nextAction nextCache nextCurrentBatch peerNextNoise)
  in MkNetworkTrainingResult nextState targets loss nextAction output

------------------------------------------------------------------------
-- Iterative CHAD reverse scan for recurrent parameter cotangents.
-- This is a gradient scan only; it does not change the one-step SARSA target.
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
    go :
      List (Int32 × Int32) -> Int32 -> List CHADFrame ->
      (Int32 × List CHADFrame)
    go [] current reverseFrames = (current , reverseFrames)
    go ((observation , localCotangent) ∷ rest) current reverseFrames =
      let cache =
            cellForward observation current inputWeight candidateWeight gateWeight
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
        chadBackward inputWeight candidateWeight gateWeight
          reverseFrames finalCotangent
  in MkCHADResult finalHidden gradient

networkApplyCHADGradient :
  IDBDConfig -> NetworkState -> CHADGradient -> NetworkState
networkApplyCHADGradient config state gradient =
  let nextInput =
        idbdStep config (qFrom64 (inputWeightGradient64 gradient))
          (networkInputParameter state)
      nextCandidate =
        idbdStep config (qFrom64 (candidateWeightGradient64 gradient))
          (networkCandidateParameter state)
      nextGate =
        idbdStep config (qFrom64 (gateWeightGradient64 gradient))
          (networkGateParameter state)
  in MkNetworkState nextInput nextCandidate nextGate (networkCritics state)

------------------------------------------------------------------------
-- Small executable checks.
------------------------------------------------------------------------

q24OneTimesOne : Bool
q24OneTimesOne = qMul qOne qOne == qOne

q24HalfTimesHalf : Bool
q24HalfTimesHalf = qMul qHalf qHalf == qQuarter

qQuantmoid4AtZero : Bool
qQuantmoid4AtZero = qQuantmoid4 0 == q63

q4TanhAtZero : Bool
q4TanhAtZero = q4Tanh 0 == 0

sarsaTerminalDoesNotBootstrap : Bool
sarsaTerminalDoesNotBootstrap =
  qSarsaOneStepTarget 123456 987654 true == 123456

sarsaNonterminalBootstrapsOnce : Bool
sarsaNonterminalBootstrapsOnce =
  qSarsaOneStepTarget 0 qOne false == qGamma

trueOnlineLambdaZeroTraceIsCurrentFeature : Bool
trueOnlineLambdaZeroTraceIsCurrentFeature =
  trueOnlineEligibilityTraceLambdaZero qHalf == qHalf

trueOnlineLambdaZeroUpdateIsOneStep : Bool
trueOnlineLambdaZeroUpdateIsOneStep =
  trueOnlineSarsaLambdaZeroUpdate qHalf qHalf qOne qOne
    == qAdd qOne qQuarter

{-# COMPILE AGDA2HS qShift #-}
{-# COMPILE AGDA2HS qOne #-}
{-# COMPILE AGDA2HS qHalf #-}
{-# COMPILE AGDA2HS qQuarter #-}
{-# COMPILE AGDA2HS qTwo #-}
{-# COMPILE AGDA2HS qFour #-}
{-# COMPILE AGDA2HS q63 #-}
{-# COMPILE AGDA2HS q126 #-}
{-# COMPILE AGDA2HS q127 #-}
{-# COMPILE AGDA2HS qPi #-}
{-# COMPILE AGDA2HS qTwoPi #-}
{-# COMPILE AGDA2HS qMax64 #-}
{-# COMPILE AGDA2HS qMin64 #-}
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
{-# COMPILE AGDA2HS qExpSmall #-}
{-# COMPILE AGDA2HS qSquare #-}
{-# COMPILE AGDA2HS qExpReduce #-}
{-# COMPILE AGDA2HS qExp #-}
{-# COMPILE AGDA2HS qSigmoid2 #-}
{-# COMPILE AGDA2HS qQuantmoid4 #-}
{-# COMPILE AGDA2HS q4Tanh #-}
{-# COMPILE AGDA2HS q4TanhGrad #-}
{-# COMPILE AGDA2HS qRelu #-}
{-# COMPILE AGDA2HS qHardSigmoid #-}
{-# COMPILE AGDA2HS qHardSigmoidGrad #-}
{-# COMPILE AGDA2HS qSarsaOneStepTarget #-}
{-# COMPILE AGDA2HS trueOnlineEligibilityTraceLambdaZero #-}
{-# COMPILE AGDA2HS trueOnlineSarsaLambdaZeroUpdate #-}
{-# COMPILE AGDA2HS Vec #-}
{-# COMPILE AGDA2HS mapVec #-}
{-# COMPILE AGDA2HS zipVecWith #-}
{-# COMPILE AGDA2HS zipVecWith3 #-}
{-# COMPILE AGDA2HS foldVec #-}
{-# COMPILE AGDA2HS qSumVec #-}
{-# COMPILE AGDA2HS qSumVec64 #-}
{-# COMPILE AGDA2HS qMean32 #-}
{-# COMPILE AGDA2HS qNat #-}
{-# COMPILE AGDA2HS indices32 #-}
{-# COMPILE AGDA2HS qCos #-}
{-# COMPILE AGDA2HS IQNQuantile #-}
{-# COMPILE AGDA2HS makeIQNQuantile #-}
{-# COMPILE AGDA2HS makeIQNBatch32 #-}
{-# COMPILE AGDA2HS IDBDConfig #-}
{-# COMPILE AGDA2HS IDBDParameter #-}
{-# COMPILE AGDA2HS idbdInitial #-}
{-# COMPILE AGDA2HS idbdStep #-}
{-# COMPILE AGDA2HS NoisyParameter #-}
{-# COMPILE AGDA2HS NoisyDense32 #-}
{-# COMPILE AGDA2HS NoisyDenseNoise32 #-}
{-# COMPILE AGDA2HS effectiveNoisyParameter #-}
{-# COMPILE AGDA2HS effectiveDenseWeights #-}
{-# COMPILE AGDA2HS noisyDenseForward #-}
{-# COMPILE AGDA2HS NonEmptyNoisyDense #-}
{-# COMPILE AGDA2HS NonEmptyNoisyDenseNoise #-}
{-# COMPILE AGDA2HS DuelingIQN32 #-}
{-# COMPILE AGDA2HS DuelingIQN32Noise #-}
{-# COMPILE AGDA2HS denseOutputs #-}
{-# COMPILE AGDA2HS nthQ #-}
{-# COMPILE AGDA2HS listCount #-}
{-# COMPILE AGDA2HS listSum64 #-}
{-# COMPILE AGDA2HS qMeanList #-}
{-# COMPILE AGDA2HS qQuantileFeatures #-}
{-# COMPILE AGDA2HS criticQuantileForAction #-}
{-# COMPILE AGDA2HS criticQuantilesForAction #-}
{-# COMPILE AGDA2HS actionMeansGo #-}
{-# COMPILE AGDA2HS criticActionMeans #-}
{-# COMPILE AGDA2HS argmaxGo #-}
{-# COMPILE AGDA2HS argmaxList #-}
{-# COMPILE AGDA2HS criticSelectAction #-}
{-# COMPILE AGDA2HS TwinDuelingCritics #-}
{-# COMPILE AGDA2HS TwinDuelingNoise #-}
{-# COMPILE AGDA2HS DoubleSARSA0Target #-}
{-# COMPILE AGDA2HS selectActiveCritic #-}
{-# COMPILE AGDA2HS selectPeerCritic #-}
{-# COMPILE AGDA2HS selectActiveNoise #-}
{-# COMPILE AGDA2HS selectPeerNoise #-}
{-# COMPILE AGDA2HS flipBool #-}
{-# COMPILE AGDA2HS doubleSARSA0Target #-}
{-# COMPILE AGDA2HS qHuber #-}
{-# COMPILE AGDA2HS qQuantileWeight #-}
{-# COMPILE AGDA2HS qQuantileHuberPair #-}
{-# COMPILE AGDA2HS qQuantileHuberPairGradient #-}
{-# COMPILE AGDA2HS qQuantileLossForCurrent #-}
{-# COMPILE AGDA2HS qQuantileGradientForCurrent #-}
{-# COMPILE AGDA2HS quantileHuberLoss32 #-}
{-# COMPILE AGDA2HS quantileHuberGradients32 #-}
{-# COMPILE AGDA2HS DenseSample32 #-}
{-# COMPILE AGDA2HS DenseGradient32 #-}
{-# COMPILE AGDA2HS zeroDenseGradient32 #-}
{-# COMPILE AGDA2HS denseGradientAccumulate #-}
{-# COMPILE AGDA2HS denseGradientFromSamples #-}
{-# COMPILE AGDA2HS makeDenseSamples #-}
{-# COMPILE AGDA2HS updateNoisyParameter #-}
{-# COMPILE AGDA2HS updateNoisyDense #-}
{-# COMPILE AGDA2HS denseGradientForBatch #-}
{-# COMPILE AGDA2HS updateNoisyDenseForBatch #-}
{-# COMPILE AGDA2HS scaleGradients #-}
{-# COMPILE AGDA2HS updateAdvantageHeads #-}
{-# COMPILE AGDA2HS criticUpdateFromQuantileGradients #-}
{-# COMPILE AGDA2HS denseSlope #-}
{-# COMPILE AGDA2HS criticHiddenSlope #-}
{-# COMPILE AGDA2HS criticHiddenCotangent #-}
{-# COMPILE AGDA2HS CellCache #-}
{-# COMPILE AGDA2HS cellForward #-}
{-# COMPILE AGDA2HS CellPullback #-}
{-# COMPILE AGDA2HS cellPullback #-}
{-# COMPILE AGDA2HS NetworkState #-}
{-# COMPILE AGDA2HS PendingDecision #-}
{-# COMPILE AGDA2HS TransitionOutput #-}
{-# COMPILE AGDA2HS NetworkTrainingResult #-}
{-# COMPILE AGDA2HS NetworkStartResult #-}
{-# COMPILE AGDA2HS networkInitialState #-}
{-# COMPILE AGDA2HS networkStart #-}
{-# COMPILE AGDA2HS makeTargetsForAction #-}
{-# COMPILE AGDA2HS networkTrainStepSARSA0 #-}
{-# COMPILE AGDA2HS CHADFrame #-}
{-# COMPILE AGDA2HS CHADGradient #-}
{-# COMPILE AGDA2HS CHADResult #-}
{-# COMPILE AGDA2HS chadForward #-}
{-# COMPILE AGDA2HS chadBackward #-}
{-# COMPILE AGDA2HS iterativeCHAD #-}
{-# COMPILE AGDA2HS networkApplyCHADGradient #-}
{-# COMPILE AGDA2HS q24OneTimesOne #-}
{-# COMPILE AGDA2HS q24HalfTimesHalf #-}
{-# COMPILE AGDA2HS qQuantmoid4AtZero #-}
{-# COMPILE AGDA2HS q4TanhAtZero #-}
{-# COMPILE AGDA2HS sarsaTerminalDoesNotBootstrap #-}
{-# COMPILE AGDA2HS sarsaNonterminalBootstrapsOnce #-}
{-# COMPILE AGDA2HS trueOnlineLambdaZeroTraceIsCurrentFeature #-}
{-# COMPILE AGDA2HS trueOnlineLambdaZeroUpdateIsOneStep #-}
