module MonolithSearch where

open import Agda.Builtin.Bool using (Bool; true; false; if_then_else_)
open import Agda.Builtin.Char using (Char; primCharEquality; primCharToNat; primNatToChar)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _<_)
open import Agda.Builtin.String using (String; primStringToList; primStringEquality)

------------------------------------------------------------------------
-- Pure declaration-search semantics for the static Pages interface.
--
-- This module owns query normalization, exact source scoping, and matching.
-- JavaScript is only the DOM adapter; Less, HTML, groff, and Fennel do not
-- implement a second search/filter algorithm.
------------------------------------------------------------------------

not : Bool → Bool
not true = false
not false = true

or : Bool → Bool → Bool
or true _ = true
or false b = b

and : Bool → Bool → Bool
and true b = b
and false _ = false

natEq : Nat → Nat → Bool
natEq zero zero = true
natEq zero (suc _) = false
natEq (suc _) zero = false
natEq (suc m) (suc n) = natEq m n

isSpace : Char → Bool
isSpace c with primCharToNat c
... | n = or (natEq n 32) (or (natEq n 9) (or (natEq n 10) (natEq n 13)))

dropLeftSpace : List Char → List Char
dropLeftSpace [] = []
dropLeftSpace (c ∷ cs) with isSpace c
... | true = dropLeftSpace cs
... | false = c ∷ cs

reverseChars : List Char → List Char
reverseChars xs = go xs []
  where
  go : List Char → List Char → List Char
  go [] acc = acc
  go (x ∷ xs) acc = go xs (x ∷ acc)

trimChars : List Char → List Char
trimChars xs = dropLeftSpace (reverseChars (dropLeftSpace (reverseChars xs)))

lowerChar : Char → Char
lowerChar c with primCharToNat c
... | n with n < 65
...   | true = c
...   | false with 90 < n
...     | true = c
...     | false = primNatToChar (n + 32)

normalize : String → List Char
normalize s = mapLower (trimChars (primStringToList s))
  where
  mapLower : List Char → List Char
  mapLower [] = []
  mapLower (c ∷ cs) = lowerChar c ∷ mapLower cs

startsWith : List Char → List Char → Bool
startsWith [] _ = true
startsWith (_ ∷ _) [] = false
startsWith (x ∷ xs) (y ∷ ys) with primCharEquality x y
... | true = startsWith xs ys
... | false = false

containsChars : List Char → List Char → Bool
containsChars _ [] = true
containsChars [] (_ ∷ _) = false
containsChars hay needle with startsWith needle hay
... | true = true
... | false with hay
...   | [] = false
...   | x ∷ xs = containsChars xs needle

contains : String → List Char → Bool
contains text needle = containsChars (normalize text) needle

sourceAllowed : String → String → Bool
sourceAllowed scope source with primStringEquality scope "learner"
... | true = primStringEquality source "FullCoupled/CanonicalLearnerMonolith.agda"
... | false with primStringEquality scope "theorem"
...   | true = primStringEquality source "FullCoupled/TheoremsMonolith.agda"
...   | false = or
      (primStringEquality source "FullCoupled/CanonicalLearnerMonolith.agda")
      (primStringEquality source "FullCoupled/TheoremsMonolith.agda")

matches : List Char → String → String → Bool
matches [] _ _ = true
matches query name signature =
  or (contains name query) (contains signature query)

filterIndicesFrom :
  Nat → List Char → String →
  List String → List String → List String → List Nat
filterIndicesFrom _ _ _ [] _ _ = []
filterIndicesFrom _ _ _ (_ ∷ _) [] _ = []
filterIndicesFrom _ _ _ (_ ∷ _) (_ ∷ _) [] = []
filterIndicesFrom index query scope (name ∷ names) (signature ∷ signatures) (source ∷ sources)
  with sourceAllowed scope source
... | false = filterIndicesFrom (suc index) query scope names signatures sources
... | true with matches query name signature
...   | true = index ∷ filterIndicesFrom (suc index) query scope names signatures sources
...   | false = filterIndicesFrom (suc index) query scope names signatures sources

-- Inputs are parallel immutable snapshots of the generated catalog. The
-- returned Nat indices select matching records without mutating the catalog.
filterIndices :
  String → String →
  List String → List String → List String → List Nat
filterIndices query scope names signatures sources =
  filterIndicesFrom zero (normalize query) scope names signatures sources
