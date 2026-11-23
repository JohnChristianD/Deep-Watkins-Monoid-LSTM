{-# OPTIONS
--cubical=erased
--erased-quotient
--lossy-unification
--syntactic-equality=1
--no-eta-equality
--no-projection-like
--no-fast-reduce
--exact-split
--rewriting
--confluence-check
#-}

------------------------------------------------------------------------
-- Pure fixed-point learner kernel.
-- Recurrent state is explicit input/output; Lua owns orchestration only.
------------------------------------------------------------------------

open import Haskell.Prelude public
open import Haskell.Data.Int public
open import Haskell.Data.Bits public
open import Agda.Builtin.Equality.Rewrite public

postulate
  S : Set
  F : Set → Set → Set
  G : (Set → Set) → Set → Set → Set
  rewF : (A : Set) → F A A ≡ S
  rewG : (A : Set → Set) (X Y : Set) → G A X Y ≡ F (A X) (A Y)
{-# REWRITE rewF rewG #-}


qShift : Int
qShift = 24

qOne : Int32
qOne = 16777216

qBeta099 : Int32
qBeta099 = 16609443

qEpsStream : Int32
qEpsStream = 65536

qGamma : Int32
qGamma = 16609443

abs32 : Int32 -> Int32
abs32 x = if x < 0 then 0 - x else x

qmul : Int32 -> Int32 -> Int32
qmul a b =
  let prod : Int64
      prod = (fromIntegral a) * (fromIntegral b)
  in fromIntegral (shiftR prod qShift)

qdivSafe : Int32 -> Int32 -> Int32
qdivSafe num den =
  if den <= 0
    then 0
    else
      let n64 : Int64
          n64 = shiftL (fromIntegral num) qShift
          d64 : Int64
          d64 = fromIntegral den
      in fromIntegral (quot n64 d64)

qdivSq64 : Int32 -> Int32 -> Int32
qdivSq64 num z =
  let den64 : Int64
      den64 = fromIntegral qOne + fromIntegral (abs32 z)
      denSq : Int64
      denSq = shiftR (den64 * den64) qShift
      num64 : Int64
      num64 = shiftL (fromIntegral num) qShift
  in if denSq <= 0 then 0 else fromIntegral (quot num64 denSq)

relu32 : Int32 -> Int32
relu32 x = if 0 < x then x else 0

softsignQ24 : Int32 -> Int32
softsignQ24 x = qdivSafe x (qOne + abs32 x)

quantmoid4Q24 : Int32 -> Int32
quantmoid4Q24 x =
  let ax = abs32 x
      cl = if ax < qOne then ax else qOne
      v64 : Int64
      v64 = fromIntegral (cl - qOne)
      vv : Int32
      vv = fromIntegral (shiftR (v64 * v64) (qShift + 1))
  in if 0 < x then qOne - vv else vv

quanttanhQ24 : Int32 -> Int32
quanttanhQ24 x = shiftL (quantmoid4Q24 x) 1 - qOne

maeCotanQ24 : Int32 -> Int32
maeCotanQ24 x = if 0 < x then qOne else if x < 0 then 0 - qOne else 0

qm4NoisyQ24 : Int32 -> Int32 -> Int32 -> Int32
qm4NoisyQ24 wSig epsIn epsOut = qmul wSig (qmul epsIn epsOut)

data IsTrue : Bool -> Set where
  IsOk : IsTrue true

@0 bornIntNonNeg : (re im : Integer) -> IsTrue (0 <= (re * re + im * im)) -> Int
bornIntNonNeg _ _ _ = 0

data StreamW : Set where
  MkSW : Int32 -> Int32 -> StreamW

data GRUReLUState : Set where
  MkGRU : Int32 -> StreamW -> StreamW -> StreamW -> StreamW -> GRUReLUState

streamStep : StreamW -> Int32 -> Int32 -> Int32 -> StreamW
streamStep (MkSW w v) delta xin lr =
  let u    = qmul delta xin
      au   = abs32 u
      vb   = qmul qBeta099 v
      vnew = if vb < au then au else vb
      upd  = qmul lr (qdivSafe u (vnew + qEpsStream))
  in MkSW (w + upd - shiftR w 18) vnew

stepIterativeChadAgda : Int32 -> GRUReLUState -> Int32 -> Int32 -> Int32 -> Int32 -> GRUReLUState
stepIterativeChadAgda raw (MkGRU h (MkSW kW vk) (MkSW rW vr) (MkSW uW vu) (MkSW oW vo)) logPi rew qNxt lr =
  let zCnn  = qmul kW raw
      feat  = softsignQ24 zCnn
      uIn   = feat + qmul uW h
      g     = quantmoid4Q24 uIn
      omg   = qOne - g
      hLin  = qmul g feat + qmul (qmul omg rW) h
      hRaw  = relu32 hLin
      hNxt  = softsignQ24 hRaw
      qCur  = qmul oW hNxt
      rTot  = rew + shiftR logPi 7
      delta = rTot + qmul qGamma qNxt - qCur
      dk    = quanttanhQ24 delta
      dLin  = if 0 < hLin then qdivSq64 (qmul dk oW) hRaw else 0
      axu   = abs32 uIn
      dgW   = if axu < qOne then qOne - axu else 0
      dG    = qmul (qmul dLin (feat - qmul rW h)) dgW
      dFeat = qmul dLin g + dG
      dCnn  = qdivSq64 dFeat zCnn
      lr2   = shiftR lr 1
  in MkGRU hNxt
       (streamStep (MkSW kW vk) dCnn raw lr2)
       (streamStep (MkSW rW vr) (qmul dLin omg) h lr2)
       (streamStep (MkSW uW vu) dG h lr2)
       (streamStep (MkSW oW vo) dk hNxt lr)

{-# COMPILE AGDA2HS qShift #-}
{-# COMPILE AGDA2HS qOne #-}
{-# COMPILE AGDA2HS qBeta099 #-}
{-# COMPILE AGDA2HS qEpsStream #-}
{-# COMPILE AGDA2HS qGamma #-}
{-# COMPILE AGDA2HS abs32 #-}
{-# COMPILE AGDA2HS qmul #-}
{-# COMPILE AGDA2HS qdivSafe #-}
{-# COMPILE AGDA2HS qdivSq64 #-}
{-# COMPILE AGDA2HS relu32 #-}
{-# COMPILE AGDA2HS softsignQ24 #-}
{-# COMPILE AGDA2HS quantmoid4Q24 #-}
{-# COMPILE AGDA2HS quanttanhQ24 #-}
{-# COMPILE AGDA2HS maeCotanQ24 #-}
{-# COMPILE AGDA2HS qm4NoisyQ24 #-}
{-# COMPILE AGDA2HS StreamW #-}
{-# COMPILE AGDA2HS GRUReLUState #-}
{-# COMPILE AGDA2HS streamStep #-}
{-# COMPILE AGDA2HS stepIterativeChadAgda #-}
