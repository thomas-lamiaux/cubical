{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.ZCohomology.CohomologyRings.S0 where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels

open import Cubical.Data.Bool
open import Cubical.Data.Nat renaming (_+_ to _+n_ ; _·_ to _·n_ ; snotz to nsnotz)
open import Cubical.Data.Int
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Vec
open import Cubical.Data.FinData

open import Cubical.Algebra.Group hiding (Unit ; ℤ; Bool ; _/_ )
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Ring
open import Cubical.Algebra.Ring.DirectProd
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Int renaming (ℤ to ℤCR)
open import Cubical.Algebra.CommRing.FGIdeal
open import Cubical.Algebra.CommRing.QuotientRing

open import Cubical.Algebra.Direct-Sum.Base
open import Cubical.Algebra.AbGroup.Instances.Direct-Sum
open import Cubical.Algebra.Polynomials.Multivariate.Base renaming (base to baseP)
open import Cubical.Algebra.CommRing.Instances.MultivariatePoly

open import Cubical.ZCohomology.RingStructure.CohomologyRing

open import Cubical.Data.Unit
open import Cubical.HITs.Sn
open import Cubical.ZCohomology.CohomologyRings.Coproduct
open import Cubical.ZCohomology.CohomologyRings.Unit

private variable
  ℓ ℓ' : Level

open Iso

-----------------------------------------------------------------------------
-- Warning
-- H*(S0) is not Z[X]/X²
-- It is Z[X]/X × Z[X]/X or Z[X] /(X² - X)
-- Beware that H*(X ⊔ Y) ≅ H*(X) × H*(Y)
-- Which would apply for H*(Unit ⊔ Unit)

ℤ[X] : CommRing ℓ-zero
ℤ[X] = PolyCommRing ℤCR 1

ℤ[x] : Type ℓ-zero
ℤ[x] = fst ℤ[X]

<X> : FinVec ℤ[x] 1
<X> zero = baseP (1 ∷ []) (CommRingStr.1r (snd ℤCR))

ℤ[X]/X : CommRing ℓ-zero
ℤ[X]/X = ℤ[X] / genIdeal ℤ[X] <X>

ℤ[x]/x : Type ℓ-zero
ℤ[x]/x = fst ℤ[X]/X


-----------------------------------------------------------------------------
-- Computation of the cohomology ring


open RingEquivs

-- Cohomology-Ring-S⁰ : RingEquiv (H*R (S₊ 0)) (DirectProd-Ring (CommRing→Ring ℤ[X]/X) (CommRing→Ring ℤ[X]/X))
-- Cohomology-Ring-S⁰ = {!!}

--                    where
--                    e1 : RingEquiv (H*R (S₊ 0)) (H*R (Unit ⊎ Unit))
--                    e1 = CohomologyRing-Equiv (invIso Iso-⊤⊎⊤-Bool)

--                    e2 : RingEquiv (H*R (Unit ⊎ Unit)) (DirectProd-Ring (H*R Unit) (H*R Unit))
--                    e2 = CohomologyRing-Coproduct Unit Unit

                   -- e3 : RingEquiv (H*R Unit) (CommRing→Ring ℤ[X]/X)  THE BUG IS HERE
                   -- e3 = {!CohomologyRing-Unit!}

                   -- e4 : RingEquiv (DirectProd-Ring (H*R Unit) (H*R Unit)) (DirectProd-Ring (CommRing→Ring ℤ[X]/X) (CommRing→Ring ℤ[X]/X))
                   -- e4 = Coproduct-Equiv.Coproduct-Equiv-12 CohomologyRing-Unit CohomologyRing-Unit
