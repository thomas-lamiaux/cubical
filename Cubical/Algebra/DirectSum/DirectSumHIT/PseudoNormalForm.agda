{-# OPTIONS --safe #-}
module Cubical.Algebra.DirectSum.DirectSumHIT.PseudoNormalForm where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport

open import Cubical.Relation.Nullary

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat renaming (_+_ to _+n_ ; _·_ to _·n_)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Vec
open import Cubical.Data.Vec.DepVec

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.DirectSumHIT
open import Cubical.Algebra.DirectSum.DirectSumHIT.Base
open import Cubical.Algebra.DirectSum.DirectSumHIT.Properties

private variable
  ℓ : Level

open GroupTheory
open AbGroupTheory
open AbGroupStr


-----------------------------------------------------------------------------
-- Notation

module _
  (G : (n : ℕ) → Type ℓ)
  (Gstr : (n : ℕ) → AbGroupStr (G n))
  where

  open AbGroupStr (snd (⊕HIT-AbGr ℕ G Gstr)) using ()
    renaming
    ( 0g       to 0⊕HIT
    ; _+_      to _+⊕HIT_
    ; -_       to -⊕HIT_
    ; assoc    to +⊕HIT-Assoc
    ; identity to +⊕HIT-IdR×IdL
    ; inverse  to +⊕HIT-InvR×InvL
    ; comm     to +⊕HIT-Comm
    ; is-set   to isSet⊕HIT)

  private
    +⊕HIT-IdR : (x : ⊕HIT ℕ G Gstr) → x +⊕HIT 0⊕HIT ≡ x
    +⊕HIT-IdR = λ x → fst (+⊕HIT-IdR×IdL x)

    +⊕HIT-IdL : (x : ⊕HIT ℕ G Gstr) → 0⊕HIT +⊕HIT x  ≡ x
    +⊕HIT-IdL = λ x → snd (+⊕HIT-IdR×IdL x)

    +⊕HIT-InvR : (x : ⊕HIT ℕ G Gstr) → x +⊕HIT (-⊕HIT x) ≡ 0⊕HIT
    +⊕HIT-InvR = λ x → fst (+⊕HIT-InvR×InvL x)

    +⊕HIT-InvL : (x : ⊕HIT ℕ G Gstr) → (-⊕HIT x) +⊕HIT x ≡ 0⊕HIT
    +⊕HIT-InvL = λ x → snd (+⊕HIT-InvR×InvL x)


-----------------------------------------------------------------------------
-- Lemma

  -- def pseudo normal form
  sumHIT : {n : ℕ} → depVec G n → ⊕HIT ℕ G Gstr
  sumHIT {0} ⋆ = 0⊕HIT
  sumHIT {suc n} (a □ dv) = (base n a) +⊕HIT (sumHIT dv)

  -- 0 and sum
  replicate0g : (n : ℕ) → depVec G n
  replicate0g (zero) = ⋆
  replicate0g (suc n) = (0g (Gstr n)) □ (replicate0g n)

  sumHIT0g : (n : ℕ) → sumHIT (replicate0g n) ≡ 0⊕HIT
  sumHIT0g (zero) = refl
  sumHIT0g (suc n) = cong₂ _+⊕HIT_ (base-neutral n) (sumHIT0g n)
                     ∙ +⊕HIT-IdL _

  -- extension and sum
  extendDVL : (k l : ℕ) → (dv : depVec G l) → depVec G (k +n l)
  extendDVL zero  l dv = dv
  extendDVL (suc k) l dv = (0g (Gstr (k +n l))) □ (extendDVL k l dv)

  extendDVLeq : (k l : ℕ) → (dv : depVec G l) → sumHIT (extendDVL k l dv) ≡ sumHIT dv
  extendDVLeq (zero)  l dv = refl
  extendDVLeq (suc k) l dv = cong (λ X → X +⊕HIT sumHIT (extendDVL k l dv)) (base-neutral (k +n l))
                             ∙ +⊕HIT-IdL _
                             ∙ extendDVLeq k l dv

  extendDVR : (k l : ℕ) → (dv : depVec G k) → depVec G (k +n l)
  extendDVR k l dv = subst (λ X → depVec G X) (+-comm l k) (extendDVL l k dv)

  extendDVReq : (k l : ℕ) → (dv : depVec G k) → sumHIT (extendDVR k l dv) ≡ sumHIT dv
  extendDVReq k l dv = {!!}

  -- pointwise add
  _pt+DV_ : {n : ℕ} → (dva dvb : depVec G n) → depVec G n
  _pt+DV_ {0} ⋆ ⋆ = ⋆
  _pt+DV_ {suc n} (a □ dva) (b □ dvb) = Gstr n ._+_ a b □ (dva pt+DV dvb)

  sumHIT+ : {n : ℕ} → (dva dvb : depVec G n) → sumHIT (dva pt+DV dvb) ≡ sumHIT dva +⊕HIT sumHIT dvb
  sumHIT+ {0} ⋆ ⋆ = sym (+⊕HIT-IdR _)
  sumHIT+ {suc n} (a □ dva) (b □ dvb) = cong₂ _+⊕HIT_ (sym (base-add _ _ _)) (sumHIT+ dva dvb)
                                        ∙ comm-4 (⊕HIT-AbGr ℕ G Gstr) _ _ _ _


-----------------------------------------------------------------------------
-- Case Traduction

  PNF : (x : ⊕HIT ℕ G Gstr) → Type ℓ
  PNF x = Σ[ m ∈ ℕ ] Σ[ dv ∈ depVec G m ] x ≡ sumHIT dv

  base→PNF : (n : ℕ) → (a : G n) → PNF (base n a)
  base→PNF n a = (suc n) , ((a □ replicate0g n) , sym (cong (λ X → base n a +⊕HIT X) (sumHIT0g n)
                  ∙ +⊕HIT-IdR _))

  add→PNF : {U V : ⊕HIT ℕ G Gstr} → (ind-U : PNF U) → (ind-V : PNF V) → PNF (U +⊕HIT V)
  add→PNF {U} {V} (k , dva , p) (l , dvb , q) =
          (k +n l)
          , (((extendDVR k l dva) pt+DV (extendDVL k l dvb))
          , cong₂ _+⊕HIT_ p q
            ∙ cong₂ _+⊕HIT_ (sym (extendDVReq k l dva)) (sym (extendDVLeq k l dvb))
            ∙ sym (sumHIT+ (extendDVR k l dva) (extendDVL k l dvb)) )

-----------------------------------------------------------------------------
-- Translation

  ⊕HIT→PNF : (x : ⊕HIT ℕ G Gstr) → Σ[ m ∈ ℕ ] Σ[ a ∈ depVec G m ] x ≡ sumHIT a
  ⊕HIT→PNF = DS-Ind-Set.f _ _ _ _
        (λ _ → isSetΣ isSetℕ (λ _ → isSetΣ {!!} λ _ → isProp→isSet (isSet⊕HIT _ _)))
        (0 , (⋆ , refl))
        base→PNF
        add→PNF
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
