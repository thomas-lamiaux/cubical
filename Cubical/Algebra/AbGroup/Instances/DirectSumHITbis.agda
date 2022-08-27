{-# OPTIONS --safe #-}
module Cubical.Algebra.AbGroup.Instances.DirectSumHITbis where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.AbGroup

open import Cubical.Algebra.DirectSum.DirectSumHIT.Base
open import Cubical.Algebra.DirectSum.DirectSumHIT.Properties
open import Cubical.Algebra.DirectSum.DirectSumHIT.PlusBis

private variable
  ℓ ℓ' : Level

module ⊕HITc (Idx : Type ℓ) (P : Idx → Type ℓ') (AGP : (r : Idx) → AbGroupStr (P r)) where

  open AbGroupStr
  open AbGroupProperties Idx P AGP
  open +BisNonDec Idx P AGP

  ⊕HIT-AbGr : AbGroup (ℓ-max ℓ ℓ')
  fst ⊕HIT-AbGr = ⊕HIT Idx P AGP
  0g (snd ⊕HIT-AbGr) = neutral
  _+_ (snd ⊕HIT-AbGr) = _addBis_
  - snd ⊕HIT-AbGr = inv
  isAbGroup (snd ⊕HIT-AbGr) = makeIsAbGroup trunc addBisAssoc addBisIdR addBisInvR addBisComm
