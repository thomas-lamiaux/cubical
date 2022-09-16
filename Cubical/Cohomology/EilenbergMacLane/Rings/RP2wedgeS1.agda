{-# OPTIONS --safe --experimental-lossy-unification #-}

module Cubical.Cohomology.EilenbergMacLane.Rings.RP2wedgeS1 where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Foundations.HLevels

open import Cubical.Relation.Nullary

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit
open import Cubical.Data.Nat hiding (_+_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Int.IsEven
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Vec
open import Cubical.Data.FinData
open import Cubical.Data.Fin

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Instances.IntMod
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.Unit
open import Cubical.Algebra.DirectSum.DirectSumHIT.Base
open import Cubical.Algebra.Ring

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.FGIdeal
open import Cubical.Algebra.CommRing.QuotientRing
open import Cubical.Algebra.CommRing.Instances.IntMod
open import Cubical.Algebra.CommRing.Instances.Polynomials.MultivariatePoly
open import Cubical.Algebra.CommRing.Instances.Polynomials.MultivariatePoly-Quotient
open import Cubical.Algebra.CommRing.Instances.Polynomials.MultivariatePoly-notationZ2

open import Cubical.HITs.Truncation
open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetQuotients as SQ renaming (_/_ to _/sq_)
open import Cubical.HITs.S1
open import Cubical.HITs.Sn
open import Cubical.HITs.RPn.Base
open import Cubical.HITs.Susp
open import Cubical.HITs.Wedge
open import Cubical.HITs.Pushout

open import Cubical.Homotopy.EilenbergMacLane.Order2

open import Cubical.Cohomology.EilenbergMacLane.Groups.KleinBottle
open import Cubical.Cohomology.EilenbergMacLane.Base
open import Cubical.Cohomology.EilenbergMacLane.CupProduct
open import Cubical.Cohomology.EilenbergMacLane.RingStructure

open Iso
open PlusBis
open RingTheory

RP²⋁S¹ : Type ℓ-zero
RP²⋁S¹ = (RP² , point) ⋁ (S₊∙ 1)

-- This notation is needed as G'' shouldn't have been put implicit
_⌣ℤ/2_ : {n m : ℕ} → coHom n ℤ/2 RP²⋁S¹ → coHom m ℤ/2 RP²⋁S¹ → coHom (n +' m) ℤ/2 RP²⋁S¹
_⌣ℤ/2_ x y = _⌣_ {G'' = ℤ/2Ring} x y

-- Pratical notations
H*ℤ/2 : {ℓ : Level} → (A : Type ℓ) → Type ℓ
H*ℤ/2 A = H* ℤ/2Ring A

H*Rℤ/2 : {ℓ : Level} → (A : Type ℓ) → Ring ℓ
H*Rℤ/2 A = H*R ℤ/2Ring A

-- He can't seem to be able to find P and AGP in some case
-- Sometimes it works, sometimes not, the reason is currently unknown
base' : (n : ℕ) → (a : coHom n ℤ/2 RP²⋁S¹) → H*ℤ/2 RP²⋁S¹
base' n a = base {Idx = ℕ} {P = λ n → coHom n ℤ/2 RP²⋁S¹} {AGP = λ n → snd (coHomGr n ℤ/2 RP²⋁S¹)} n a


{- Convention over ℤ[X,Y]
   X : (1,0)
   Y : (0,1)
-}

module Equiv-RP²⋁S¹-Properties
  (e₀ : AbGroupIso ℤ/2 (coHomGr 0 ℤ/2 RP²⋁S¹))
  (e₁ : AbGroupIso (dirProdAb ℤ/2 ℤ/2) (coHomGr 1 ℤ/2 RP²⋁S¹))
  (e₂ : AbGroupIso ℤ/2 (coHomGr 2 ℤ/2 RP²⋁S¹))
  (eₙ₊₃ : (n : ℕ) → (3 ≤ n) → AbGroupIso (coHomGr n ℤ/2 RP²⋁S¹) (UnitAbGroup {ℓ = ℓ-zero}))
  where


-----------------------------------------------------------------------------
-- Definitions, Import with notations

  -- Import with notation
  open IsGroupHom
  open AbGroupStr

  open CommRingStr (snd ℤ/2CommRing) using ()
    renaming
    ( 0r        to 0ℤ/2
    ; 1r        to 1ℤ/2
    ; _+_       to _+ℤ/2_
    ; -_        to -ℤ/2_
    ; _·_       to _·ℤ/2_
    ; +Assoc    to +ℤ/2Assoc
    ; +IdL      to +ℤ/2IdL
    ; +IdR      to +ℤ/2IdR
    ; +Comm     to +ℤ/2Comm
    ; ·Assoc    to ·ℤ/2Assoc
    ; ·IdL      to ·ℤ/2IdL
    ; ·IdR      to ·ℤ/2IdR
    ; ·DistR+   to ·ℤ/2DistR+
    ; ·Comm     to ·ℤ/2Comm
    ; is-set    to isSetℤ/2     )

  <Y³,XY,X²> : FinVec ℤ/2[x,y] 3
  <Y³,XY,X²> zero  = base (0 ∷ 3 ∷ []) 1ℤ/2
  <Y³,XY,X²> one   = base (1 ∷ 1 ∷ []) 1ℤ/2
  <Y³,XY,X²> two   = base (2 ∷ 0 ∷ []) 1ℤ/2

  ℤ/2[X,Y]/<Y³,XY,X²> : CommRing ℓ-zero
  ℤ/2[X,Y]/<Y³,XY,X²> = PolyCommRing-Quotient ℤ/2CommRing <Y³,XY,X²>

  ℤ/2[x,y]/<2y,y²,xy,x²> : Type ℓ-zero
  ℤ/2[x,y]/<2y,y²,xy,x²> = fst ℤ/2[X,Y]/<Y³,XY,X²>

  open RingStr (snd (H*Rℤ/2 RP²⋁S¹)) using ()
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

  open CommRingStr (snd ℤ/2[X,Y]) using ()
    renaming
    ( 0r        to 0Pℤ/2
    ; 1r        to 1Pℤ/2
    ; _+_       to _+Pℤ/2_
    ; -_        to -Pℤ/2_
    ; _·_       to _·Pℤ/2_
    ; +Assoc    to +Pℤ/2Assoc
    ; +IdL      to +Pℤ/2IdL
    ; +IdR      to +Pℤ/2IdR
    ; +Comm     to +Pℤ/2Comm
    ; ·Assoc    to ·Pℤ/2Assoc
    ; ·IdL      to ·Pℤ/2IdL
    ; ·IdR      to ·Pℤ/2IdR
    ; ·Comm     to ·Pℤ/2Comm
    ; ·DistR+   to ·Pℤ/2DistR+
    ; is-set    to isSetPℤ/2     )

  open CommRingStr (snd ℤ/2[X,Y]/<Y³,XY,X²>) using ()
    renaming
    ( 0r        to 0Pℤ/2I
    ; 1r        to 1Pℤ/2I
    ; _+_       to _+Pℤ/2I_
    ; -_        to -Pℤ/2I_
    ; _·_       to _·Pℤ/2I_
    ; +Assoc    to +Pℤ/2IAssoc
    ; +IdL      to +Pℤ/2IIdL
    ; +IdR      to +Pℤ/2IIdR
    ; +Comm     to +Pℤ/2IComm
    ; ·Assoc    to ·Pℤ/2IAssoc
    ; ·IdL      to ·Pℤ/2IIdL
    ; ·IdR      to ·Pℤ/2IIdR
    ; ·DistR+   to ·Pℤ/2IDistR+
    ; is-set    to isSetPℤ/2I     )


  ϕ₀ = fun (fst e₀)
  ϕ₀str = snd e₀
  ϕ₀⁻¹ = inv (fst e₀)
  ϕ₀⁻¹str = snd (invGroupIso e₀)
  ϕ₀-sect = rightInv (fst e₀)
  ϕ₀-retr = leftInv (fst e₀)

  ϕ₁ = fun (fst e₁)
  ϕ₁str = snd e₁
  ϕ₁⁻¹ = inv (fst e₁)
  ϕ₁⁻¹str = snd (invGroupIso e₁)
  ϕ₁-sect = rightInv (fst e₁)
  ϕ₁-retr = leftInv (fst e₁)

  ϕ₂ = fun (fst e₂)
  ϕ₂str = snd e₂
  ϕ₂⁻¹ = inv (fst e₂)
  ϕ₂⁻¹str = snd (invGroupIso e₂)
  ϕ₂-sect = rightInv (fst e₂)
  ϕ₂-retr = leftInv (fst e₂)

  ϕ₁left : fst ℤ/2 → coHom 1 ℤ/2 RP²⋁S¹
  ϕ₁left a = ϕ₁ (a , 0ℤ/2)

  ϕ₁leftStr : IsGroupHom (snd (AbGroup→Group ℤ/2)) ϕ₁left (snd (AbGroup→Group (coHomGr 1 ℤ/2 RP²⋁S¹)))
  ϕ₁leftStr = makeIsGroupHom (λ a b → pres· ϕ₁str _ _)

  ϕ₁right : fst ℤ/2 → coHom 1 ℤ/2 RP²⋁S¹
  ϕ₁right b = ϕ₁ (0ℤ/2 , b)

  ϕ₁rightStr : IsGroupHom (snd (AbGroup→Group ℤ/2)) ϕ₁right (snd (AbGroup→Group (coHomGr 1 ℤ/2 RP²⋁S¹)))
  ϕ₁rightStr = makeIsGroupHom (λ a b → pres· ϕ₁str _ _)

  module CompPoperties
    (ϕ₀-pres1 : ϕ₀ 1ℤ/2 ≡ 1ₕ {G'' = ℤ/2Ring})
    (ϕ₁-1010-notTrivial : (ϕ₁ (1ℤ/2 , 0ℤ/2)) ⌣ℤ/2 (ϕ₁ (1ℤ/2 , 0ℤ/2)) ≡ ϕ₂ 1ℤ/2)
    (ϕ₁-0101-trivial : (ϕ₁ (0ℤ/2 , 1ℤ/2) ⌣ℤ/2 ϕ₁ (0ℤ/2 , 1ℤ/2)) ≡ (0ₕ 2))
    (ϕ₁-1001-trivial : (ϕ₁ (1ℤ/2 , 0ℤ/2) ⌣ℤ/2 ϕ₁ (0ℤ/2 , 1ℤ/2)) ≡ (0ₕ 2))
    (ϕ₁-0110-trivial : (ϕ₁ (0ℤ/2 , 1ℤ/2) ⌣ℤ/2 ϕ₁ (1ℤ/2 , 0ℤ/2)) ≡ (0ₕ 2))
    where

  -----------------------------------------------------------------------------
  -- Direct Sens on ℤ/2[x,y]


    ℤ/2[x,y]→H*-RP²⋁S¹ : ℤ/2[x,y] → (H*ℤ/2  RP²⋁S¹)
    ℤ/2[x,y]→H*-RP²⋁S¹ = DS-Rec-Set.f _ _ _ _ isSetH*
                        0H*
                        ϕ
                        _+H*_
                        +H*Assoc
                        +H*IdR
                        +H*Comm
                        base-neutral-eq
                        base-add-eq
     where
     ϕ : _
     ϕ (zero        ∷ zero              ∷ []) a = base 0 (ϕ₀ a)
     ϕ (zero        ∷ one               ∷ []) a = base 1 (ϕ₁ (a , 0ℤ/2))
     ϕ (zero        ∷ two               ∷ []) a = base 2 (ϕ₂ a)
     ϕ (zero        ∷ suc (suc (suc m)) ∷ []) a = 0H*
     ϕ (one         ∷ zero              ∷ []) a = base 1 (ϕ₁ (0ℤ/2 , a))
     ϕ (one         ∷ suc m             ∷ []) a = 0H*
     ϕ (suc (suc n) ∷ m                 ∷ []) a = 0H*

     base-neutral-eq : _
     base-neutral-eq (zero        ∷ zero              ∷ []) = cong (base 0) (pres1 ϕ₀str) ∙ base-neutral _
     base-neutral-eq (zero        ∷ one               ∷ []) = cong (base 1) (pres1 ϕ₁str) ∙ base-neutral _
     base-neutral-eq (zero        ∷ two               ∷ []) = cong (base 2) (pres1 ϕ₂str) ∙ base-neutral _
     base-neutral-eq (zero        ∷ suc (suc (suc m)) ∷ []) = refl
     base-neutral-eq (one         ∷ zero              ∷ []) = cong (base 1) (pres1 ϕ₁str) ∙ base-neutral _
     base-neutral-eq (one         ∷ suc m             ∷ []) = refl
     base-neutral-eq (suc (suc n) ∷ m                 ∷ []) = refl

     base-add-eq : _
     base-add-eq (zero        ∷ zero              ∷ []) a b = base-add _ _ _ ∙ cong (base 0) (sym ((pres· ϕ₀str _ _)))
     base-add-eq (zero        ∷ one               ∷ []) a b = base-add _ _ _ ∙ cong (base' 1) ((sym (pres· ϕ₁str _ _)))
     base-add-eq (zero        ∷ two               ∷ []) a b = base-add 2 (ϕ₂ a) (ϕ₂ b) ∙ cong (base' 2) (sym (pres· ϕ₂str _ _))
     base-add-eq (zero        ∷ suc (suc (suc m)) ∷ []) a b = +H*IdR _
     base-add-eq (one         ∷ zero              ∷ []) a b = base-add _ _ _ ∙ cong (base' 1) ((sym (pres· ϕ₁str _ _)))
     base-add-eq (one         ∷ suc m             ∷ []) a b = +H*IdR _
     base-add-eq (suc (suc n) ∷ m                 ∷ []) a b = +H*IdR _



  -----------------------------------------------------------------------------
  -- Morphism on ℤ/2[x]

    ℤ/2[x,y]→H*-RP²⋁S¹-pres1 : ℤ/2[x,y]→H*-RP²⋁S¹ (1Pℤ/2) ≡ 1H*
    ℤ/2[x,y]→H*-RP²⋁S¹-pres1 = cong (base 0) ϕ₀-pres1

    ℤ/2[x,y]→H*-RP²⋁S¹-pres+ : (x y : ℤ/2[x,y]) → ℤ/2[x,y]→H*-RP²⋁S¹ (x +Pℤ/2 y) ≡ ℤ/2[x,y]→H*-RP²⋁S¹ x +H* ℤ/2[x,y]→H*-RP²⋁S¹ y
    ℤ/2[x,y]→H*-RP²⋁S¹-pres+ x y = refl

--     --           Explanation of the product proof
--     --
--     --           -------------------------------------------------------
--     --           | (0,0) | (0,1) | (0,m+2) | (1,0) | (1,m+1) | (n+2,m) |
--     -- -----------------------------------------------------------------
--     -- | (0,0)   |   H⁰  |   H⁰  |    0    |   H⁰  |    0    |    0    |
--     -- -----------------------------------------------------------------
--     -- | (0,1)   |  Sym  |   0₄  |    0    |   0₃  |    0    |    0    |
--     -- -----------------------------------------------------------------
--     -- | (0,m+2) | ==========================================> triv    |
--     -- -----------------------------------------------------------------
--     -- | (1,0)   |  Sym  |  Sym  |    0    |   ★  |    0    |    0    |
--     -- -----------------------------------------------------------------
--     -- | (1,m+1) | ==========================================> triv    |
--     -- -----------------------------------------------------------------
--     -- | (n+2,m) | ==========================================> triv    |
--     -- -----------------------------------------------------------------


    ϕ₀⌣IdL : {n : ℕ} → (f : coHom n ℤ/2 RP²⋁S¹) → ϕ₀ (1ℤ/2) ⌣ℤ/2 f ≡ f
    ϕ₀⌣IdL f = cong (λ X → X ⌣ℤ/2 f) ϕ₀-pres1 ∙ 1ₕ-⌣ {G'' = ℤ/2Ring} _ f

    lem-ϕ₀⌣ : (a b : fst ℤ/2) → {n : ℕ} → (ϕₙ : fst ℤ/2 → coHom n ℤ/2 RP²⋁S¹) →
              (ϕₙstr : IsGroupHom (snd (ℤGroup/ 2) ) ϕₙ (snd (AbGroup→Group (coHomGr n ℤ/2 RP²⋁S¹))))
               → ϕ₀ a ⌣ℤ/2 ϕₙ b ≡ ϕₙ (a ·ℤ/2 b)
    lem-ϕ₀⌣ a b ϕₙ ϕₙstr = ℤ/2-elim {A = λ a → ϕ₀ a ⌣ℤ/2 ϕₙ b ≡ ϕₙ (a ·ℤ/2 b)}
                          (cong (λ X → X ⌣ℤ/2 ϕₙ b) (pres1 ϕ₀str)
                            ∙ 0ₕ-⌣ _ _ _
                            ∙ sym (pres1 ϕₙstr)
                            ∙ cong ϕₙ (sym (0LeftAnnihilates ℤ/2Ring _)))
                          (ϕ₀⌣IdL _ ∙ cong ϕₙ (sym (·ℤ/2IdL _)))
                          a

    foo : AbGroup ℓ-zero
    foo = ℤ/2

    fo : AbGroup ℓ-zero
    fo = coHomGr 1 ℤ/2 RP²⋁S¹


    unitGroupEq : {n : ℕ} → (e : AbGroupIso (coHomGr n ℤ/2 RP²⋁S¹) (UnitAbGroup {ℓ = ℓ-zero})) →
                     (x y : coHom n ℤ/2 RP²⋁S¹) → x ≡ y
    unitGroupEq {n} e x y = isOfHLevelRetractFromIso {ℓ' = ℓ-zero} 1 (fst e) isPropUnit* _ _

    module _
      {n m : ℕ}
      (ϕₙ : fst ℤ/2 → coHom n ℤ/2 RP²⋁S¹)
      (ϕₙstr : IsGroupHom (snd (ℤGroup/ 2) ) ϕₙ (snd (AbGroup→Group (coHomGr n ℤ/2 RP²⋁S¹))))
      (ϕₘ : fst ℤ/2 → coHom m ℤ/2 RP²⋁S¹)
      (ϕₘstr : IsGroupHom (snd (ℤGroup/ 2) ) ϕₘ (snd (AbGroup→Group (coHomGr m ℤ/2 RP²⋁S¹))))
      (ϕₙ₊ₘ : fst ℤ/2 → coHom (n +' m) ℤ/2 RP²⋁S¹)
      (ϕₙ₊ₘstr : IsGroupHom (snd (ℤGroup/ 2) ) ϕₙ₊ₘ (snd (AbGroup→Group (coHomGr (n +' m) ℤ/2 RP²⋁S¹))))
      (cup-comp : ϕₙ 1ℤ/2 ⌣ℤ/2 ϕₘ 1ℤ/2 ≡ ϕₙ₊ₘ 1ℤ/2)
      where

      ϕₙ⌣ϕₘ-notTrivial : (a b : fst ℤ/2) → ϕₙ a ⌣ℤ/2 ϕₘ b ≡ ϕₙ₊ₘ (a ·ℤ/2 b)
      ϕₙ⌣ϕₘ-notTrivial = {!!}

    module _
      {n m : ℕ}
      (ϕₙ : fst ℤ/2 → coHom n ℤ/2 RP²⋁S¹)
      (ϕₙstr : IsGroupHom (snd (ℤGroup/ 2) ) ϕₙ (snd (AbGroup→Group (coHomGr n ℤ/2 RP²⋁S¹))))
      (ϕₘ : fst ℤ/2 → coHom m ℤ/2 RP²⋁S¹)
      (ϕₘstr : IsGroupHom (snd (ℤGroup/ 2) ) ϕₘ (snd (AbGroup→Group (coHomGr m ℤ/2 RP²⋁S¹))))
      (cup-comp : ϕₙ 1ℤ/2 ⌣ℤ/2 ϕₘ 1ℤ/2 ≡ 0ₕ (n +' m))
      where

      ϕₙ⌣ϕₘ-Trivial : (a b : fst ℤ/2) → ϕₙ a ⌣ℤ/2 ϕₘ b ≡ 0ₕ (n +' m)
      ϕₙ⌣ϕₘ-Trivial = {!!}



    -- note that the proof might be simpliale by adding a second partition on T
    -- side, though it might complicated a bunch of things
    pres·-int : (n m : ℕ) → (a : fst ℤ/2) → (k l : ℕ) → (b : fst ℤ/2) →
                   ℤ/2[x,y]→H*-RP²⋁S¹ (base (n ∷ m ∷ []) a ·Pℤ/2 base (k ∷ l ∷ []) b)
                ≡ ℤ/2[x,y]→H*-RP²⋁S¹ (base (n ∷ m ∷ []) a) cup ℤ/2[x,y]→H*-RP²⋁S¹ (base (k ∷ l ∷ []) b)
    -- non trivial case (0,0)
    pres·-int zero zero a zero zero b = cong (base' 0) (sym (lem-ϕ₀⌣ _ _ ϕ₀ ϕ₀str))
    pres·-int zero zero a zero one b = cong (base' 1) (sym (lem-ϕ₀⌣ _ _ ϕ₁left ϕ₁leftStr))
    pres·-int zero zero a zero two b = cong (base' 2) (sym (lem-ϕ₀⌣ _ _ ϕ₂ ϕ₂str))
    pres·-int zero zero a zero (suc (suc (suc l))) b = refl
    pres·-int zero zero a one zero b = cong (base' 1) (sym (lem-ϕ₀⌣ _ _ (λ b → ϕ₁ (0ℤ/2 , b))
                                                      (makeIsGroupHom (λ a b → pres· ϕ₁str _ _))))
    pres·-int zero zero a one (suc l) b = refl
    pres·-int zero zero a (suc (suc k)) l b = refl
    -- case (0,1) not trivial
    pres·-int zero one a zero zero b = cong (base' 1) (sym (ϕₙ⌣ϕₘ-notTrivial
                                       ϕ₁left ϕ₁leftStr ϕ₀ ϕ₀str ϕ₁left ϕ₁leftStr
                                       ((cong (λ X → ϕ₁left 1ℤ/2 ⌣ℤ/2 X) {!ϕ₀str!}) ∙ {!!})
                                       _ _))
      -- case α²
    pres·-int zero one a zero one b = cong (base' 2) (sym (ϕₙ⌣ϕₘ-notTrivial ϕ₁left ϕ₁leftStr ϕ₁left ϕ₁leftStr ϕ₂ ϕ₂str ϕ₁-1010-notTrivial a b))
    pres·-int zero one a zero two b = sym (base-neutral _) ∙ cong (base' 3) (unitGroupEq (eₙ₊₃ 3 (0 , refl)) _ _)
    pres·-int zero one a zero (suc (suc (suc l))) b = refl
      -- case αβ
    pres·-int zero one a one zero b = sym (cong (base' 2) (ϕₙ⌣ϕₘ-Trivial ϕ₁left ϕ₁leftStr ϕ₁right ϕ₁rightStr ϕ₁-1001-trivial a b) ∙ base-neutral 2)
    pres·-int zero one a one (suc l) b = refl
    pres·-int zero one a (suc (suc k)) l b = refl
    -- case (0,2) trivial right, by trivial goups
    pres·-int zero two a zero zero b = {!0 case!}
    pres·-int zero two a zero one b = sym (base-neutral _) ∙ cong (base' 3) (unitGroupEq (eₙ₊₃ 3 (0 , refl)) _ _)
    pres·-int zero two a zero two b = sym (base-neutral _) ∙ cong (base' 4) (unitGroupEq (eₙ₊₃ 4 (1 , refl)) _ _)
    pres·-int zero two a zero (suc (suc (suc l))) b = refl
    pres·-int zero two a one zero b = sym (base-neutral _) ∙ cong (base' 3) (unitGroupEq (eₙ₊₃ 3 (0 , refl)) _ _)
    pres·-int zero two a one (suc l) b = refl
    pres·-int zero two a (suc (suc k)) l b = refl
    -- case (0,m+2) trivial left, by def
    pres·-int zero (suc (suc (suc m))) a zero zero b = refl
    pres·-int zero (suc (suc (suc m))) a zero one b = refl
    pres·-int zero (suc (suc (suc m))) a zero two b = refl
    pres·-int zero (suc (suc (suc m))) a zero (suc (suc (suc l))) b = refl
    pres·-int zero (suc (suc (suc m))) a one zero b = refl
    pres·-int zero (suc (suc (suc m))) a one (suc l) b = refl
    pres·-int zero (suc (suc (suc m))) a (suc (suc k)) l b = refl
    -- case (1,0) not trivial
    pres·-int one zero a zero zero b = {!because 0!}
      -- case βα
    pres·-int one zero a zero one b = sym (cong (base' 2) (ϕₙ⌣ϕₘ-Trivial ϕ₁right ϕ₁rightStr ϕ₁left ϕ₁leftStr ϕ₁-0110-trivial a b) ∙ base-neutral _)
    pres·-int one zero a zero two b = sym (base-neutral _) ∙ cong (base' 3) (unitGroupEq (eₙ₊₃ 3 (0 , refl)) _ _)
    pres·-int one zero a zero (suc (suc (suc l))) b = refl
      -- case β²
    pres·-int one zero a one zero b = sym (cong (base' 2) (ϕₙ⌣ϕₘ-Trivial ϕ₁right ϕ₁rightStr ϕ₁right ϕ₁rightStr ϕ₁-0101-trivial a b) ∙ base-neutral _)
    pres·-int one zero a one (suc l) b = refl
    pres·-int one zero a (suc (suc k)) l b = refl
    -- case (1,m+1) trivial left, by def
    pres·-int one (suc m) a zero l b = refl
    pres·-int one (suc m) a (suc k) l b = refl
    -- case (1,m+1) trivial left, by def
    pres·-int (suc (suc n)) m a k l b = refl

--     pres·-base-case-vec : (v : Vec ℕ 2) → (a : ℤ) → (v' : Vec ℕ 2) → (b : ℤ) →
--                              ℤ[x,y]→H*-RP²⋁S¹ (base v a ·Pℤ base v' b)
--                           ≡ ℤ[x,y]→H*-RP²⋁S¹ (base v a) cup ℤ[x,y]→H*-RP²⋁S¹ (base v' b)
--     pres·-base-case-vec (n ∷ m ∷ []) a (k ∷ l ∷ []) b = pres·-int n m a k l b

--     -- proof of the morphism
--     ℤ[x,y]→H*-RP²⋁S¹-pres· : (x y : ℤ[x,y]) → ℤ[x,y]→H*-RP²⋁S¹ (x ·Pℤ y) ≡ ℤ[x,y]→H*-RP²⋁S¹ x cup ℤ[x,y]→H*-RP²⋁S¹ y
--     ℤ[x,y]→H*-RP²⋁S¹-pres· = DS-Ind-Prop.f _ _ _ _
--                            (λ x p q i y j → isSetH* _ _ (p y) (q y) i j)
--                            (λ y → refl)
--                            base-case
--                            λ {U V} ind-U ind-V y → cong₂ _+H*_ (ind-U y) (ind-V y)
--       where
--       base-case : _
--       base-case v a = DS-Ind-Prop.f _ _ _ _ (λ _ → isSetH* _ _)
--                              (sym (RingTheory.0RightAnnihilates (H*R RP²⋁S¹) _))
--                              (λ v' b → pres·-base-case-vec v a v' b )
--                              λ {U V} ind-U ind-V → (cong₂ _+H*_ ind-U ind-V) ∙ sym (·H*DistR+ _ _ _)


--   -----------------------------------------------------------------------------
--   -- Function on ℤ[x]/x + morphism

--     -- not a trivial cancel ?
--     ℤ[x,y]→H*-RP²⋁S¹-cancel : (x : Fin 4) → ℤ[x,y]→H*-RP²⋁S¹ (<Y³,XY,X²> x) ≡ 0H*
--     ℤ[x,y]→H*-RP²⋁S¹-cancel zero = cong (base 2) (pres1 ϕ₂str) ∙ base-neutral _
--     ℤ[x,y]→H*-RP²⋁S¹-cancel one = refl
--     ℤ[x,y]→H*-RP²⋁S¹-cancel two = refl
--     ℤ[x,y]→H*-RP²⋁S¹-cancel three = refl


--     ℤ[X,Y]→H*-RP²⋁S¹ : RingHom (CommRing→Ring ℤ[X,Y]) (H*R RP²⋁S¹)
--     fst ℤ[X,Y]→H*-RP²⋁S¹ = ℤ[x,y]→H*-RP²⋁S¹
--     snd ℤ[X,Y]→H*-RP²⋁S¹ = makeIsRingHom ℤ[x,y]→H*-RP²⋁S¹-pres1
--                                        ℤ[x,y]→H*-RP²⋁S¹-pres+
--                                        ℤ[x,y]→H*-RP²⋁S¹-pres·

--     -- hence not a trivial pres+, yet pres0 still is
--     ℤ[X,Y]/<Y³,XY,X²>→H*R-RP²⋁S¹ : RingHom (CommRing→Ring ℤ[X,Y]/<Y³,XY,X²>) (H*R RP²⋁S¹)
--     ℤ[X,Y]/<Y³,XY,X²>→H*R-RP²⋁S¹ = Quotient-FGideal-CommRing-Ring.inducedHom
--                                     ℤ[X,Y] (H*R RP²⋁S¹) ℤ[X,Y]→H*-RP²⋁S¹
--                                     <Y³,XY,X²> ℤ[x,y]→H*-RP²⋁S¹-cancel

--     ℤ[x,y]/<2y,y²,xy,x²>→H*-RP²⋁S¹ : ℤ[x,y]/<2y,y²,xy,x²> → H* RP²⋁S¹
--     ℤ[x,y]/<2y,y²,xy,x²>→H*-RP²⋁S¹ = fst ℤ[X,Y]/<Y³,XY,X²>→H*R-RP²⋁S¹

--     ℤ[x,y]/<2y,y²,xy,x²>→H*-RP²⋁S¹-pres0 : ℤ[x,y]/<2y,y²,xy,x²>→H*-RP²⋁S¹ 0PℤI ≡ 0H*
--     ℤ[x,y]/<2y,y²,xy,x²>→H*-RP²⋁S¹-pres0 = refl

--     ℤ[x,y]/<2y,y²,xy,x²>→H*-RP²⋁S¹-pres+ : (x y : ℤ[x,y]/<2y,y²,xy,x²>) →
--                                              ℤ[x,y]/<2y,y²,xy,x²>→H*-RP²⋁S¹ ( x +PℤI y)
--                                           ≡ ℤ[x,y]/<2y,y²,xy,x²>→H*-RP²⋁S¹ x +H* ℤ[x,y]/<2y,y²,xy,x²>→H*-RP²⋁S¹ y
--     ℤ[x,y]/<2y,y²,xy,x²>→H*-RP²⋁S¹-pres+ x y = IsRingHom.pres+ (snd ℤ[X,Y]/<Y³,XY,X²>→H*R-RP²⋁S¹) x y


--   -----------------------------------------------------------------------------
--   -- Converse Sens on H* → ℤ[X,Y]

--     ψ₂⁻¹ : Bool → ℤ
--     ψ₂⁻¹ false = 1
--     ψ₂⁻¹ true = 0

--     private
--     -- Those lemma are requiered because ψ₂⁻¹
--     -- is a morphism only under the quotient
--       Λ : (x : Bool) → ℤ[x,y]/<2y,y²,xy,x²>
--       Λ x = [ (base (0 ∷ 1 ∷ []) (ψ₂⁻¹ x)) ]

--       Λ-pres+ : (x y : Bool) → Λ x +PℤI Λ y ≡ Λ (x +Bool y)
--       Λ-pres+ false false = cong [_] (base-add _ _ _)
--                             ∙ eq/ (base (0 ∷ 1 ∷ []) 2)
--                                   (base (0 ∷ 1 ∷ []) 0)
--                                   ∣ ((λ {zero → base (0 ∷ 0 ∷ []) 1 ; one → 0Pℤ ; two → 0Pℤ ; three → 0Pℤ}) , helper) ∣₁
--               where
--               helper : _
--               helper = base-add  _ _ _
--                        ∙ sym (cong₂ _+Pℤ_ refl (+PℤIdL _ ∙ +PℤIdL _ ∙ +PℤIdL _) ∙ +PℤIdR _)
--       Λ-pres+ false true = cong [_] (base-add _ _ _)
--       Λ-pres+ true false = cong [_] (base-add _ _ _)
--       Λ-pres+ true true = cong [_] (base-add _ _ _)

--     ϕ⁻¹ : (k : ℕ) → (a : coHom k RP²⋁S¹) → ℤ[x,y]/<2y,y²,xy,x²>
--     ϕ⁻¹ zero a = [ base (0 ∷ 0 ∷ []) (ϕ₀⁻¹ a) ]
--     ϕ⁻¹ one a = [ base (1 ∷ 0 ∷ []) (ϕ₁⁻¹ a) ]
--     ϕ⁻¹ two a = [ base (0 ∷ 1 ∷ []) ((ψ₂⁻¹ ∘ ϕ₂⁻¹) a) ]
--     ϕ⁻¹ (suc (suc (suc k))) a = 0PℤI

--     H*-RP²⋁S¹→ℤ[x,y]/<2y,y²,xy,x²> : H* RP²⋁S¹ → ℤ[x,y]/<2y,y²,xy,x²>
--     H*-RP²⋁S¹→ℤ[x,y]/<2y,y²,xy,x²> = DS-Rec-Set.f _ _ _ _ isSetPℤI
--          0PℤI
--          ϕ⁻¹
--          _+PℤI_
--          +PℤIAssoc
--          +PℤIIdR
--          +PℤIComm
--          base-neutral-eq
--          base-add-eq
--       where

--       base-neutral-eq : _
--       base-neutral-eq zero = cong [_] (cong (base {AGP = λ _ → snd ℤAG} (0 ∷ 0 ∷ [])) (pres1 ϕ₀⁻¹str)
--                                        ∙ (base-neutral _))
--       base-neutral-eq one = cong [_] (cong (base {AGP = λ _ → snd ℤAG} (1 ∷ 0 ∷ [])) (pres1 ϕ₁⁻¹str)
--                                        ∙ (base-neutral _))
--       base-neutral-eq two = cong [_] (cong (base (0 ∷ 1 ∷ [])) (cong ψ₂⁻¹ (pres1 ϕ₂⁻¹str))
--                                      ∙ base-neutral _)
--       base-neutral-eq (suc (suc (suc k))) = refl

--       base-add-eq : _
--       base-add-eq zero a b = cong [_] (base-add _ _ _ ∙ cong (base (0 ∷ 0 ∷ [])) (sym (pres· ϕ₀⁻¹str _ _)))
--       base-add-eq one a b = cong [_] (base-add _ _ _ ∙ cong (base (1 ∷ 0 ∷ [])) (sym (pres· ϕ₁⁻¹str _ _)))
--       base-add-eq two a b = Λ-pres+ (ϕ₂⁻¹ a) (ϕ₂⁻¹ b)
--                             ∙ cong [_] (cong (base (0 ∷ 1 ∷ [])) (cong ψ₂⁻¹ (sym (pres· ϕ₂⁻¹str _ _))))
--       base-add-eq (suc (suc (suc k))) a b = +PℤIIdR _

--     H*-RP²⋁S¹→ℤ[x,y]/<2y,y²,xy,x²>-pres0 : H*-RP²⋁S¹→ℤ[x,y]/<2y,y²,xy,x²> 0H* ≡ 0PℤI
--     H*-RP²⋁S¹→ℤ[x,y]/<2y,y²,xy,x²>-pres0 = refl

--     H*-RP²⋁S¹→ℤ[x,y]/<2y,y²,xy,x²>-pres+ : (x y : H* RP²⋁S¹) →
--                                                H*-RP²⋁S¹→ℤ[x,y]/<2y,y²,xy,x²> (x +H* y)
--                                            ≡ (H*-RP²⋁S¹→ℤ[x,y]/<2y,y²,xy,x²> x) +PℤI (H*-RP²⋁S¹→ℤ[x,y]/<2y,y²,xy,x²> y)
--     H*-RP²⋁S¹→ℤ[x,y]/<2y,y²,xy,x²>-pres+ x y = refl



--   -----------------------------------------------------------------------------
--   -- Section

--     ψ₂-sect : (x : Bool) → ψ₂ (ψ₂⁻¹ x) ≡ x
--     ψ₂-sect false = refl
--     ψ₂-sect true = refl


--     e-sect-base : (k : ℕ) → (a : coHom k RP²⋁S¹) →
--                   ℤ[x,y]/<2y,y²,xy,x²>→H*-RP²⋁S¹ (ϕ⁻¹ k a) ≡ base k a
--     e-sect-base zero a = cong (base 0) (ϕ₀-sect a)
--     e-sect-base one a = cong (base 1) (ϕ₁-sect a)
--     e-sect-base two a = cong (base 2) (cong ϕ₂ (ψ₂-sect _) ∙ ϕ₂-sect a)
--     e-sect-base (suc (suc (suc k))) a = sym (base-neutral (suc (suc (suc k))))
--                                         ∙ cong (base (suc (suc (suc k)))) (unitGroupEq (Hⁿ-RP²⋁S¹≅0 k) _ _)

--     e-sect : (x : H* RP²⋁S¹) → ℤ[x,y]/<2y,y²,xy,x²>→H*-RP²⋁S¹ (H*-RP²⋁S¹→ℤ[x,y]/<2y,y²,xy,x²> x) ≡ x
--     e-sect = DS-Ind-Prop.f _ _ _ _ (λ _ → isSetH* _ _)
--              refl
--              e-sect-base
--              λ {U V} ind-U ind-V → ℤ[x,y]/<2y,y²,xy,x²>→H*-RP²⋁S¹-pres+ _ _ ∙ cong₂ _+H*_ ind-U ind-V



--   -----------------------------------------------------------------------------
--   -- Retraction

--     e-retr-ψ₂-false : (a : ℤ) → (isEven a ≡ false) → Λ (ψ₂ a) ≡ [ base (0 ∷ 1 ∷ []) a ]
--     e-retr-ψ₂-false a x = cong [_] (cong (base (0 ∷ 1 ∷ [])) (cong ψ₂⁻¹ x))
--                     ∙ eq/ (base (0 ∷ 1 ∷ []) 1) (base (0 ∷ 1 ∷ []) a)
--                       ∣ ((λ {zero → base (0 ∷ 0 ∷ []) (-ℤ m) ; one → 0Pℤ ; two → 0Pℤ ; three → 0Pℤ}) , helper) ∣₁
--               where
--               m = fst (isEvenFalse a x)

--               helper : _
--               helper = base-add _ _ _
--                        ∙ cong (base (0 ∷ 1 ∷ [])) (cong (λ X → 1 +ℤ (-ℤ X)) (snd (isEvenFalse a x))
--                                                ∙ cong (λ X → 1 +ℤ X) (-Dist+ _ _)
--                                                ∙ +ℤAssoc _ _ _
--                                                ∙ +ℤIdL _)
--                        ∙ sym (cong₂ _+Pℤ_ (cong (base (0 ∷ 1 ∷ [])) (sym (-DistL· _ _) ∙ cong -ℤ_ (·ℤComm _ _)))
--                                           (+PℤIdL _ ∙ +PℤIdL _ ∙ +PℤIdL _)
--                              ∙ +PℤIdR _)

--     e-retr-ψ₂-true : (a : ℤ) → (isEven a ≡ true) → Λ (ψ₂ a) ≡ [ base (0 ∷ 1 ∷ []) a ]
--     e-retr-ψ₂-true a x = cong [_] (cong (base (0 ∷ 1 ∷ [])) (cong ψ₂⁻¹ x))
--                     ∙ eq/ (base (0 ∷ 1 ∷ []) 0) (base (0 ∷ 1 ∷ []) a)
--                       ∣ ((λ {zero → base (0 ∷ 0 ∷ []) (-ℤ m) ; one → 0Pℤ ; two → 0Pℤ ; three → 0Pℤ}) , helper) ∣₁
--               where
--               m = fst (isEvenTrue a x)

--               helper : _
--               helper = base-add _ _ _
--                        ∙ cong (base (0 ∷ 1 ∷ [])) (+ℤIdL _ ∙ cong -ℤ_ (snd (isEvenTrue a x)))
--                        ∙ sym (cong₂ _+Pℤ_ (cong (base (0 ∷ 1 ∷ [])) (sym (-DistL· _ _) ∙ cong -ℤ_ (·ℤComm _ _)))
--                                           (+PℤIdL _ ∙ +PℤIdL _ ∙ +PℤIdL _)
--                              ∙ +PℤIdR _)


--     e-retr-ψ₂ : (a : ℤ) → ((isEven a ≡ false) ⊎ (isEven a ≡ true)) → Λ (ψ₂ a) ≡ [ base (0 ∷ 1 ∷ []) a ]
--     e-retr-ψ₂ a (inl x) = e-retr-ψ₂-false a x
--     e-retr-ψ₂ a (inr x) = e-retr-ψ₂-true a x



--     e-retr-base : (v : Vec ℕ 2) → (a : ℤ) →
--                   H*-RP²⋁S¹→ℤ[x,y]/<2y,y²,xy,x²> (ℤ[x,y]/<2y,y²,xy,x²>→H*-RP²⋁S¹ [ base v a ]) ≡ [ base v a ]
--     e-retr-base (zero        ∷ zero        ∷ []) a = cong [_] (cong (base (0 ∷ 0 ∷ [])) (ϕ₀-retr a))
--     e-retr-base (zero        ∷ one         ∷ []) a = cong [_] (cong (base (0 ∷ 1 ∷ [])) (cong ψ₂⁻¹ (ϕ₂-retr (ψ₂ a))))
--                                                       ∙ e-retr-ψ₂ a (dichotomyBoolSym (isEven a))
--     e-retr-base (zero        ∷ suc (suc m) ∷ []) a = eq/ _ _ ∣ (v , helper) ∣₁
--            where
--            v = λ { zero → 0Pℤ ; one → base (0 ∷ m ∷ []) (-ℤ a) ; two → 0Pℤ ; three → 0Pℤ }
--            helper : _
--            helper = +PℤIdL _ ∙ sym (+PℤIdL _
--                     ∙ cong₂ _+Pℤ_ (cong₂ base (cong (λ X → 0 ∷ X ∷ []) (+-comm _ _)) (·ℤIdR _))
--                                   (+PℤIdL _ ∙ +PℤIdL _) ∙ +PℤIdR _)
--     e-retr-base (one         ∷ zero        ∷ []) a = cong [_] (cong (base (1 ∷ 0 ∷ [])) (ϕ₁-retr a))
--     e-retr-base (one         ∷ suc m       ∷ []) a = eq/ _ _ ∣ (v , helper) ∣₁
--            where
--            v = λ { zero → 0Pℤ ; one → 0Pℤ ; two → base (0 ∷ m ∷ []) (-ℤ a) ; three → 0Pℤ }
--            helper : _
--            helper = +PℤIdL _ ∙ sym (+PℤIdL _ ∙ +PℤIdL _
--                     ∙ cong₂ _+Pℤ_ (cong₂ base (cong (λ X → 1 ∷ X ∷ []) (+-comm _ _)) (·ℤIdR _)) (+PℤIdL _) ∙ +PℤIdR _)
--     e-retr-base (suc (suc n) ∷ m           ∷ []) a = eq/ _ _ ∣ (v , helper) ∣₁
--            where
--            v = λ {zero → 0Pℤ ; one → 0Pℤ ; two → 0Pℤ ; three → base (n ∷ m ∷ []) (-ℤ a) }
--            helper : _
--            helper = +PℤIdL _ ∙ sym (+PℤIdL _ ∙ +PℤIdL _ ∙ +PℤIdL _ ∙ +PℤIdR _
--                     ∙ cong₂ base (cong₂ (λ X → λ Y → X ∷ Y ∷ []) (+-comm _ _) (+-comm _ _)) (·ℤIdR _))

--     e-retr : (x : ℤ[x,y]/<2y,y²,xy,x²>) → H*-RP²⋁S¹→ℤ[x,y]/<2y,y²,xy,x²> (ℤ[x,y]/<2y,y²,xy,x²>→H*-RP²⋁S¹ x) ≡ x
--     e-retr = SQ.elimProp (λ _ → isSetPℤI _ _)
--              (DS-Ind-Prop.f _ _ _ _ (λ _ → isSetPℤI _ _)
--              refl
--              e-retr-base
--              λ {U V} ind-U ind-V → cong₂ _+PℤI_ ind-U ind-V)



-- -- Computation of the Cohomology Ring

-- module _ where

--   open Equiv-RP²⋁S¹-Properties (invGroupIso H¹-RP²⋁S¹≅ℤ) (invGroupIso H²-RP²⋁S¹≅Bool)
--   open pres⌣trivial
--   open PblComp (λ a b → sym (ϕₙ⌣ϕₘ-0 ϕ₁ ϕ₁str ϕ₁ ϕ₁str trivial-cup a b))

--   RP²⋁S¹-CohomologyRing : RingEquiv (CommRing→Ring ℤ[X,Y]/<Y³,XY,X²>) (H*R RP²⋁S¹)
--   fst RP²⋁S¹-CohomologyRing = isoToEquiv is
--     where
--     is : Iso ℤ[x,y]/<2y,y²,xy,x²> (H* RP²⋁S¹)
--     fun is = ℤ[x,y]/<2y,y²,xy,x²>→H*-RP²⋁S¹
--     inv is = H*-RP²⋁S¹→ℤ[x,y]/<2y,y²,xy,x²>
--     rightInv is = e-sect
--     leftInv is = e-retr
--   snd RP²⋁S¹-CohomologyRing = snd ℤ[X,Y]/<Y³,XY,X²>→H*R-RP²⋁S¹

--   CohomologyRing-RP²⋁S¹ : RingEquiv (H*R RP²⋁S¹) (CommRing→Ring ℤ[X,Y]/<Y³,XY,X²>)
--   CohomologyRing-RP²⋁S¹ = RingEquivs.invRingEquiv RP²⋁S¹-CohomologyRing
