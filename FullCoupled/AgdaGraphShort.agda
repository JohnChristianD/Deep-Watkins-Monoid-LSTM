module FullCoupled.AgdaGraphShort where




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


import FullCoupled.CanonicalLearnerMonolith as C
import FullCoupled.TheoremsMonolith as T

LearnerState = C.CanonicalFullLearnerState
LearnerKernel = C.CanonicalFullLearnerKernel

step = C.canonicalFullStep
policy = C.canonicalPolicy
affine = C.applyMonoidAffine
lstm = C.runMonoidLSTMCell
planAssoc = T.aStar-plan-append-associative
