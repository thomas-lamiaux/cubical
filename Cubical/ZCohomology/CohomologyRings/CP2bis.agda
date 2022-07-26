{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.ZCohomology.CohomologyRings.CP2bis where

{- Warning this file compute the cohomology up to a missing lemma.
   Lemma that is to be added soon
-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Foundations.HLevels

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit
open import Cubical.Data.Nat renaming (_+_ to _+n_ ; +-comm to +n-comm ; _·_ to _·n_ ; snotz to nsnotz)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Int hiding (_+'_)
open import Cubical.Data.Sigma
open import Cubical.Data.Vec
open import Cubical.Data.FinData

open import Cubical.Relation.Nullary

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Instances.Int
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.DirectSum.DirectSumHIT.Base
open import Cubical.Algebra.Ring
open import Cubical.Algebra.Ring.Ideal
open import Cubical.Algebra.Ring.Kernel
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Ideal hiding (IdealsIn)
open import Cubical.Algebra.CommRing.FGIdeal
open import Cubical.Algebra.Polynomials.Multivariate.Base
open import Cubical.Algebra.CommRing.Instances.Int renaming (ℤCommRing to ℤCR)
open import Cubical.Algebra.CommRing.Instances.Polynomials.MultivariatePoly
open import Cubical.Algebra.CommRing.Instances.Polynomials.MultivariatePoly-Quotient
open import Cubical.Algebra.CommRing.Instances.Polynomials.MultivariatePoly-notationZ

open import Cubical.HITs.SetQuotients as SQ renaming (_/_ to _/sq_)
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.Truncation
open import Cubical.HITs.Sn

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.RingStructure.CupProduct
open import Cubical.ZCohomology.RingStructure.RingLaws
open import Cubical.ZCohomology.RingStructure.CohomologyRing
open import Cubical.ZCohomology.Groups.CP2
open import Cubical.ZCohomology.CohomologyRings.CupProductProperties

open Iso
open gradedRingProperties

module ComputeCP²Notation
  (e₀ : GroupIso ℤGroup (coHomGr 0 CP²))
  (e₂ : GroupIso ℤGroup (coHomGr 2 CP²))
  (e₄ : GroupIso ℤGroup (coHomGr 4 CP²))
  where

  open IsGroupHom

-----------------------------------------------------------------------------
-- Begin Notation

  ---------------------------------------------------------------------------
  -- Import Notation

  open CommRingStr (snd ℤCR) using ()
    renaming
    ( 0r        to 0ℤ
    ; 1r        to 1ℤ
    ; _+_       to _+ℤ_
    ; -_        to -ℤ_
    ; _·_       to _·ℤ_
    ; +Assoc    to +ℤAssoc
    ; +IdL      to +ℤIdL
    ; +IdR      to +ℤIdR
    ; +Comm     to +ℤComm
    ; ·Assoc    to ·ℤAssoc
    ; ·IdL      to ·ℤIdL
    ; ·IdR      to ·ℤIdR
    ; ·DistR+   to ·ℤDistR+
    ; is-set    to isSetℤ     )

  open RingStr (snd (H*R CP²)) using ()
    renaming
    ( 0r        to 0H*
    ; 1r        to 1H*
    ; _+_       to _+H*_
    ; -_        to -H*_
    ; _·_       to _cup_
    ; +Assoc    to +H*Assoc
    ; +IdL      to +H*IdL
    ; +IdR      to +H*IdR
    ; +Comm     to +H*Comm
    ; ·Assoc    to ·H*Assoc
    ; ·IdL      to ·H*IdL
    ; ·IdR      to ·H*IdR
    ; ·DistR+   to ·H*DistR+
    ; is-set    to isSetH*     )

  open CommRingStr (snd ℤ[X]) using ()
    renaming
    ( 0r        to 0Pℤ
    ; 1r        to 1Pℤ
    ; _+_       to _+Pℤ_
    ; -_        to -Pℤ_
    ; _·_       to _·Pℤ_
    ; +Assoc    to +PℤAssoc
    ; +IdL      to +PℤIdL
    ; +IdR      to +PℤIdR
    ; +Comm     to +PℤComm
    ; ·Assoc    to ·PℤAssoc
    ; ·IdL      to ·PℤIdL
    ; ·IdR      to ·PℤIdR
    ; ·Comm     to ·PℤComm
    ; ·DistR+   to ·PℤDistR+
    ; is-set    to isSetPℤ     )

  open CommRingStr (snd ℤ[X]/X³) using ()
    renaming
    ( 0r        to 0PℤI
    ; 1r        to 1PℤI
    ; _+_       to _+PℤI_
    ; -_        to -PℤI_
    ; _·_       to _·PℤI_
    ; +Assoc    to +PℤIAssoc
    ; +IdL      to +PℤIIdL
    ; +IdR      to +PℤIIdR
    ; +Comm     to +PℤIComm
    ; ·Assoc    to ·PℤIAssoc
    ; ·IdL      to ·PℤIIdL
    ; ·IdR      to ·PℤIIdR
    ; ·DistR+   to ·PℤIDistR+
    ; is-set    to isSetPℤI     )


  ---------------------------------------------------------------------------
  -- Equiv Notation

  ϕ₀ : ℤ → coHom 0 CP²
  ϕ₀ = fun (fst e₀)
  ϕ₀str = snd e₀
  ϕ₂ : ℤ → coHom 2 CP²
  ϕ₂ = fun (fst e₂)
  ϕ₂str = snd e₂
  ϕ₄ : ℤ → coHom 4 CP²
  ϕ₄ = fun (fst e₄)
  ϕ₄str = snd e₄

  ϕ₀⁻¹ = inv (fst e₀)
  ϕ₀⁻¹str = snd (invGroupIso e₀)
  ϕ₂⁻¹ = inv (fst e₂)
  ϕ₂⁻¹str = snd (invGroupIso e₂)
  ϕ₄⁻¹ = inv (fst e₄)
  ϕ₄⁻¹str = snd (invGroupIso e₄)

  ϕ₀-sect = rightInv (fst e₀)
  ϕ₂-sect = rightInv (fst e₂)
  ϕ₄-sect = rightInv (fst e₄)

  ϕ₀-retr = leftInv (fst e₀)
  ϕ₂-retr = leftInv (fst e₂)
  ϕ₄-retr = leftInv (fst e₄)


-- End Notation
-----------------------------------------------------------------------------



-----------------------------------------------------------------------------
-- Begin proof of the equivalence

  open pres⌣

  -- assumption
  module ComputeCP²Function
    (ϕ₀-pres1 : ϕ₀ 1ℤ ≡ 1⌣)
    (ϕ₀-gen : (n : ℕ) → (a : coHom n CP²) → ϕ₀ (pos 1) ⌣ a ≡ a)
    (eq⌣224 : ϕ₂ (pos 1) ⌣ ϕ₂ (pos 1) ≡ ϕ₄ (pos 1))
    where


  -----------------------------------------------------------------------------
  -- Direct Sens on ℤ[x]/<X³>

    -- Function on ℤ[x]
    ℤ[x]→H*-CP² : ℤ[x] → H* CP²
    ℤ[x]→H*-CP² = DS-Rec-Set.f _ _ _ _ isSetH*
         0H*
         ϕ
         _+H*_
         +H*Assoc
         +H*IdR
         +H*Comm
         base-neutral-eq
         base-add-eq
      where
      ϕ : (v : Vec ℕ 1) → (a : ℤ) → H* CP²
      ϕ (zero ∷ []) a = base 0 (ϕ₀ a)
      ϕ (one ∷ []) a  = base 2 (ϕ₂ a)
      ϕ (two ∷ []) a  = base 4 (ϕ₄ a)
      ϕ (suc (suc (suc k)) ∷ []) a = 0H*

      base-neutral-eq : _
      base-neutral-eq (zero ∷ []) = cong (base 0) (pres1 ϕ₀str) ∙ base-neutral _
      base-neutral-eq (one ∷ [])  = cong (base 2) (pres1 ϕ₂str) ∙ base-neutral _
      base-neutral-eq (two ∷ [])  = cong (base 4) (pres1 ϕ₄str) ∙ base-neutral _
      base-neutral-eq (suc (suc (suc k)) ∷ []) = refl

      base-add-eq : _
      base-add-eq (zero ∷ []) a b = base-add _ _ _ ∙ cong (base 0) (sym (pres· ϕ₀str _ _))
      base-add-eq (one ∷ []) a b  = base-add _ _ _ ∙ cong (base 2) (sym (pres· ϕ₂str _ _))
      base-add-eq (two ∷ []) a b  = base-add _ _ _ ∙ cong (base 4) (sym (pres· ϕ₄str _ _))
      base-add-eq (suc (suc (suc k)) ∷ []) a b = +H*IdR _


  -----------------------------------------------------------------------------
  -- Morphism Properties

    ℤ[x]→H*-CP²-pres1 : ℤ[x]→H*-CP² (1Pℤ) ≡ 1H*
    ℤ[x]→H*-CP²-pres1 = cong (base 0) ϕ₀-pres1


    ℤ[x]→H*-CP²-map+ : (x y : ℤ[x]) → ℤ[x]→H*-CP² (x +Pℤ y) ≡ ℤ[x]→H*-CP² x +H* ℤ[x]→H*-CP² y
    ℤ[x]→H*-CP²-map+ x y = refl


    presCupInt : (k : ℕ) → (a : ℤ) → (l : ℕ) → (b : ℤ) →
                   ℤ[x]→H*-CP² (base (k ∷ []) a ·Pℤ base (l ∷ []) b)
                 ≡ ℤ[x]→H*-CP² (base (k ∷ []) a) cup ℤ[x]→H*-CP² (base (l ∷ []) b)
    presCupInt zero a zero b = cong (base 0) (ϕₙ⌣ϕₘ ϕ₀ ϕ₀str ϕ₀ ϕ₀str ϕ₀ ϕ₀str (ϕ₀-gen _ _) _ _)
    presCupInt zero a one b  = cong (base 2) ((ϕₙ⌣ϕₘ ϕ₀ ϕ₀str ϕ₂ ϕ₂str ϕ₂ ϕ₂str (ϕ₀-gen _ _) _ _))
    presCupInt zero a two b  = cong (base 4) ((ϕₙ⌣ϕₘ ϕ₀ ϕ₀str ϕ₄ ϕ₄str ϕ₄ ϕ₄str (ϕ₀-gen _ _) _ _))
    presCupInt zero a (suc (suc (suc l))) b = refl
    presCupInt one a zero b = cong ℤ[x]→H*-CP² (·PℤComm (base (one ∷ []) a) (base (zero ∷ []) b))
                              ∙ presCupInt zero b one a
                              ∙ gradCommRing CP² _ _ _ _
    presCupInt one a one b  = cong (base 4) ((ϕₙ⌣ϕₘ ϕ₂ ϕ₂str ϕ₂ ϕ₂str ϕ₄ ϕ₄str eq⌣224 _ _))
    presCupInt one a two b  = sym (base-neutral _)
                              ∙ cong (base 6) (trivialGroupEq (Hⁿ-CP²≅0 _ (compute-eqℕ _ _) (compute-eqℕ _ _)) _ _)
    presCupInt one a (suc (suc (suc l))) b = refl
    presCupInt two a zero b = cong ℤ[x]→H*-CP² (·PℤComm (base (two ∷ []) a) (base (zero ∷ []) b))
                              ∙ presCupInt zero b two a
                              ∙ gradCommRing CP² _ _ _ _
    presCupInt two a one b  = sym (base-neutral _)
                              ∙ cong (base 6) (trivialGroupEq (Hⁿ-CP²≅0 _ (compute-eqℕ _ _) (compute-eqℕ _ _)) _ _)
    presCupInt two a two b  = sym (base-neutral _)
                              ∙ cong (base 8) (trivialGroupEq (Hⁿ-CP²≅0 _ (compute-eqℕ _ _) (compute-eqℕ _ _)) _ _)
    presCupInt two a (suc (suc (suc l))) b = refl
    presCupInt (suc (suc (suc k))) a l b = refl


    presCupVec : (v : Vec ℕ 1) → (a : ℤ) → (v' : Vec ℕ 1) → (b : ℤ) →
                  ℤ[x]→H*-CP² (base v a ·Pℤ base v' b)
                ≡ ℤ[x]→H*-CP² (base v a) cup ℤ[x]→H*-CP² (base v' b)
    presCupVec (k ∷ []) a (l ∷ []) b = presCupInt k a l b


    -- proof
    presCup : (x y : ℤ[x]) → ℤ[x]→H*-CP² (x ·Pℤ y) ≡ ℤ[x]→H*-CP² x cup ℤ[x]→H*-CP² y
    presCup = DS-Ind-Prop.f _ _ _ _
                           (λ x p q i y j → isSetH* _ _ (p y) (q y) i j)
                           (λ y → refl)
                           base-case
                           λ {U V} ind-U ind-V y → cong₂ _+H*_ (ind-U y) (ind-V y)
      where
      base-case : _
      base-case (k ∷ []) a = DS-Ind-Prop.f _ _ _ _ (λ _ → isSetH* _ _)
                             (sym (RingTheory.0RightAnnihilates (H*R CP²) _))
                             (λ v' b → presCupVec (k ∷ []) a v' b)
                             λ {U V} ind-U ind-V → (cong₂ _+H*_ ind-U ind-V) ∙ sym (·H*DistR+ _ _ _)



    ℤ[X]→H*-CP² : RingHom (CommRing→Ring ℤ[X]) (H*R CP²)
    fst ℤ[X]→H*-CP² = ℤ[x]→H*-CP²
    snd ℤ[X]→H*-CP² = makeIsRingHom ℤ[x]→H*-CP²-pres1 ℤ[x]→H*-CP²-map+ presCup

  -----------------------------------------------------------------------------
  -- Computing Kernel

    -- Proof that <X³> is in Ker(T)
    <X³>Ideal : IdealsIn (CommRing→Ring ℤ[X])
    <X³>Ideal = CommIdeal→Ideal (generatedIdeal ℤ[X] <X³>)

    ℤ[x]→H*-CP²-cancelX : (k : Fin 1) → ℤ[x]→H*-CP² (<X³> k) ≡ 0H*
    ℤ[x]→H*-CP²-cancelX zero = refl



    -- adg : (x : ℤ[x]) → kernel ℤ[X]→H*-CP² x ≡ fst <X³>Ideal x
    -- adg = {!!}

    -- implies that <X³> is incude because of Ring structure

    -- -- Proving that Ker(T) is in <X³>

    LinComb→Ker : (x : ℤ[x]) → isLinearCombination ℤ[X] <X³> x → ℤ[x]→H*-CP² x ≡ 0H*
    LinComb→Ker x = PT.rec (isSetH* _ _)
                     λ { (a , p) → cong ℤ[x]→H*-CP² p
                     ∙ cancelLinearCombination ℤ[X] (H*R CP²) ℤ[X]→H*-CP² 1
                       a <X³> λ { zero → refl } }

    Ker→LinCom : (x : ℤ[x]) → (p : ℤ[x]→H*-CP² x ≡ 0H*) → isLinearCombination ℤ[X] <X³> x
    Ker→LinCom = DS-Ind-Prop.f _ _ _ _ (λ _ → isPropΠ (λ _ → squash₁))
             (λ p → ∣ ((λ { zero → 0Pℤ }) , sym (+PℤIdR _)) ∣₁)
             base-eq
             λ {U V} → {!!}
             -- ok, on peut en extraire a, b prendre add + sep

           where
           base-eq : _
           base-eq (zero ∷ []) a p = ∣ ((λ { zero → 0Pℤ }) , sym pp) ∣₁  -- ϕ₀ a ≡ 0 => a ≡ 0 because ϕ₀ iso
             where
             pp : _
             pp = +PℤIdR _ ∙ sym (base-neutral (zero ∷ [])) ∙ cong (base (0 ∷ [])) {!!}
           base-eq (one ∷ []) a p = ∣ ((λ { zero → 0Pℤ }) , {!!}) ∣₁
           base-eq (two ∷ []) a p = ∣ ((λ { zero → 0Pℤ }) , {!!}) ∣₁
           base-eq (suc (suc (suc n)) ∷ []) a p = ∣ ((λ { zero → base (n ∷ []) a }) , sym q) ∣₁
             where
             q : _
             q = +PℤIdR _ ∙ cong₂ base (cong (λ X → X ∷ []) (+n-comm _ _)) (·ℤIdR _)
