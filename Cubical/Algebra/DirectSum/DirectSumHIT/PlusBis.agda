{-# OPTIONS --safe #-}
module Cubical.Algebra.DirectSum.DirectSumHIT.PlusBis where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sigma
open import Cubical.Data.Nat hiding (_+_)
open import Cubical.Data.Int using (ℤ ; discreteℤ) renaming (-_ to -ℤ_)

open import Cubical.Relation.Nullary

open import Cubical.Algebra.Monoid.Instances.Nat
open import Cubical.Algebra.Group
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.DirectSum.DirectSumHIT.Base
open import Cubical.Algebra.AbGroup.Instances.DirectSumHIT
open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Int

ℤAbGroup = Ring→AbGroup (CommRing→Ring ℤCommRing)

private variable
  ℓ ℓ' : Level



-----------------------------------------------------------------------------
-- Examples for the computation

ℤ[x] = ⊕HIT ℕ (λ _ → ℤ) (λ _ → snd ℤAbGroup)

module Examples
  (base' :  ℕ → ℤ → ℤ[x])
  (inv' : ℤ[x] → ℤ[x])
  (_add'_ : ℤ[x] → ℤ[x] → ℤ[x])
  where

  -- open AbGroupStr (snd (⊕HIT-AbGr ℕ(λ _ → ℤ) (λ _ → snd ℤAbGroup)))


  -- First Exmaple of noramisation
  -- P = 4X + 5X²
  PNorm0 : ⊕HIT ℕ (λ _ → ℤ) (λ _ → snd ℤAbGroup)
  PNorm0 = base 1 4 add base 5 8

  -- P1 = ((0 + 0) + (4X + 0)) + (5X⁵ + 0)
  P1 : ⊕HIT ℕ (λ _ → ℤ) (λ _ → snd ℤAbGroup)
  P1 = ((neutral add neutral) add (base 1 4 add neutral)) add ((base 5 8) add neutral)

  P1' : ⊕HIT ℕ (λ _ → ℤ) (λ _ → snd ℤAbGroup)
  P1' = ((neutral add' neutral) add' (base' 1 4 add' neutral)) add' ((base' 5 8) add' neutral)

  -- P2 = (4X + 0) + (((0 + 0) + 0) + 8X⁵)
  P2 : ⊕HIT ℕ (λ _ → ℤ) (λ _ → snd ℤAbGroup)
  P2 = ((base 1 4) add neutral) add (((neutral add neutral) add neutral) add (base 5 8))

  P2' : ⊕HIT ℕ (λ _ → ℤ) (λ _ → snd ℤAbGroup)
  P2' = ((base' 1 4) add' neutral) add' (((neutral add' neutral) add' neutral) add' (base' 5 8))


  -- Q = 17 + X^2
  QNorm0 : ⊕HIT ℕ (λ _ → ℤ) (λ _ → snd ℤAbGroup)
  QNorm0 = base 1 17 add base 2 1

  -- Q1 = 12X + (5X + X²)
  Q1' : ⊕HIT ℕ (λ _ → ℤ) (λ _ → snd ℤAbGroup)
  Q1' = base' 1 17 add' (base' 0 0 add' base' 2 1)

  -- Q2 = 12X + (5X + (0 + X²))
  Q2' : ⊕HIT ℕ (λ _ → ℤ) (λ _ → snd ℤAbGroup)
  Q2' = base' 1 12 add' (base' 1 5 add' (base' 0 0 add' base' 2 1))

  -- Q3 = (12X + (0 + (5X + 0))) + (0X + X²)
  Q3' : ⊕HIT ℕ (λ _ → ℤ) (λ _ → snd ℤAbGroup)
  Q3' = (base' 1 12 add' (neutral add' (base' 1 5 add' neutral))) add' (base' 0 0 add' base' 2 1)

  Q4' : ⊕HIT ℕ (λ _ → ℤ) (λ _ → snd ℤAbGroup)
  Q4' = (base' 1 12 add' (neutral add' (base' 1 5 add' neutral))) add' (((base' 0 4) add' base 0 (-ℤ 4)) add' base' 2 1)

  -- some combination to normalise
  R = P1 add' P1'
  Rinv = P1' add' P1
  T = P1' add' Q2'
  U = P1' add' (inv' P1')



-----------------------------------------------------------------------------
-- Improvement without any hypothesis

module +BisNonDec
  (Idx : Type ℓ)
  (G    : Idx → Type ℓ')
  (Gstr : (r : Idx) → AbGroupStr (G r))
  where

  open AbGroupStr (snd (⊕HIT-AbGr Idx G Gstr))

  Norm0 : (x : ⊕HIT Idx G Gstr) → (y : ⊕HIT Idx G Gstr) → Σ[ z ∈ ⊕HIT Idx G Gstr ] (x add y ≡ z)
  Norm0 = DS-Ind-Prop.f _ _ _ _ (λ _ → isPropΠ (λ _ → isPropSingl))
          (λ y → y , (+IdL _))
          (λ k a → DS-Ind-Prop.f _ _ _ _ (λ _ → isPropSingl)
                    ((base k a) , (+IdR _))
                    (λ l b → (base k a add base l b) , refl)
                    λ {U} {V} ind-U ind-V → (base k a add (U add V)) , refl)
          λ {U V} ind-U ind-V y → fst (ind-U (fst (ind-V y))) ,
                                   sym (+Assoc _ _ _)
                                   ∙ cong (λ X → U add X) (snd (ind-V y))
                                   ∙ snd (ind-U (fst (ind-V y)))


  _addBis_ : ⊕HIT Idx G Gstr → ⊕HIT Idx G Gstr → ⊕HIT Idx G Gstr
  _addBis_ x y = fst (Norm0 x y)

  addBis≡Add : (x y : ⊕HIT Idx G Gstr) → x addBis y ≡ x add y
  addBis≡Add x y = sym (snd (Norm0 x y))

  -- AbGroup Properties of addBis
  addBisAssoc : (x y z : ⊕HIT Idx G Gstr) → x addBis (y addBis z) ≡ (x addBis y) addBis z
  addBisAssoc x y z = addBis≡Add x (y addBis z)
                      ∙ cong (λ X → x add X) (addBis≡Add y z)
                      ∙ +Assoc x y z
                      ∙ cong (λ X → X add z) (sym (addBis≡Add x y))
                      ∙ sym (addBis≡Add (x addBis y) z)

  addBisIdR : (x : ⊕HIT Idx G Gstr) → x addBis neutral ≡ x
  addBisIdR x = addBis≡Add x neutral ∙ addRid x

  addBisInvR : (x : ⊕HIT Idx G Gstr) → x addBis (- x) ≡ neutral
  addBisInvR x = addBis≡Add x (- x) ∙ +InvR x

  addBisComm : (x y : ⊕HIT Idx G Gstr) → x addBis y ≡ y addBis x
  addBisComm x y = addBis≡Add x y ∙ +Comm x y ∙ sym (addBis≡Add y x)

  -- gives a normalisation procedure
  applyNorm0 : ⊕HIT Idx G Gstr → ⊕HIT Idx G Gstr
  applyNorm0 = DS-Rec-Set.f _ _ _ _ trunc
               neutral base _addBis_
               addBisAssoc addBisIdR addBisComm
               base-neutral base-add


-- Examples :
module GeneralExamples where
  open AbGroupStr (snd (⊕HIT-AbGr ℕ(λ _ → ℤ) (λ _ → snd ℤAbGroup)))
  open +BisNonDec ℕ(λ _ → ℤ) (λ _ → snd ℤAbGroup)
  open Examples base (-_) (_addBis_)

  P1'≡PNorm0 : P1' ≡ PNorm0
  P1'≡PNorm0 = refl

  P2'≡PNorm0 : P2' ≡ PNorm0
  P2'≡PNorm0 = refl

  Norm0P1≡PNorm0 : applyNorm0 P1 ≡ PNorm0
  Norm0P1≡PNorm0 = refl

  Q3'≡Q2' : Q3' ≡ Q2'
  Q3'≡Q2' = refl

  -- Q2'≡Q1' : Q2' ≡ Q1'
  -- Q2'≡Q1' = {!refl!}
  -- error 12 != 17
  -- => this doesn't contract "base"

  -- Q1'≡QNorm0 : Q1' ≡ QNorm0
  -- Q1'≡QNorm0 = {!refl!}
  -- error : base 0 0 add base 2 1 != base 2 1
  -- => doesn't simplify base n 0

  -- U≡neutral : U ≡ neutral
  -- U≡neutral = {!refl!}
  -- Big bug, nothing simplifie exacte the 0

  R' = R
  Rinv' = Rinv
  T' = T
  U' = U

-----------------------------------------------------------------------------
-- With aditional decidable properties for polynomials

module +BisPol
  (Idx : Type ℓ)
  (G    : Type ℓ')
  (Gstr : AbGroupStr G)
  (discreteIdx : Discrete Idx)
  (discreteG : Discrete G)
  where

  open AbGroupStr

  -- Base Bis, compute on a
  baseBis : (r : Idx) → G → ⊕HIT Idx (λ _ → G) (λ _ → Gstr)
  baseBis r a with discreteG a (0g Gstr)
  ... | yes p = neutral
  ... | no ¬p = base r a

  base≡baseBis : (r : Idx) → (a : G) → base r a ≡ baseBis r a
  base≡baseBis r a with discreteG a (0g Gstr)
  ... | yes p = cong (base r) p ∙ base-neutral r
  ... | no ¬p = refl

  -- Plus Bis, compute on 0 and base
  Norm0 : (x y : ⊕HIT Idx (λ _ → G) (λ _ → Gstr)) → Σ[ z ∈ ⊕HIT Idx (λ _ → G) (λ _ → Gstr) ] (x add y ≡ z)
  Norm0 = DS-Ind-Prop.f _ _ _ _ (λ _ → isPropΠ (λ _ → isPropSingl))
          (λ y → y , +IdL (snd (⊕HIT-AbGr Idx (λ _ → G) (λ _ → Gstr))) _)
          (λ k a → DS-Ind-Prop.f _ _ _ _ (λ _ → isPropSingl)
                    ((baseBis k a) , +IdR (snd (⊕HIT-AbGr Idx (λ _ → G) (λ _ → Gstr))) _ ∙ (base≡baseBis _ _))  -- *
                    (λ l b → cbnBaseBase k l a b)
                    λ {U} {V} ind-U ind-V → cbnBaseAdd k a V U)
          λ {U V} ind-U ind-V y → fst (ind-U (fst (ind-V y))) ,
                                   sym (+Assoc (snd (⊕HIT-AbGr Idx (λ _ → G) (λ _ → Gstr))) _ _ _ )
                                   ∙ cong (λ X → U add X) (snd (ind-V y))
                                   ∙ snd (ind-U (fst (ind-V y)))

    where
    cbnBaseBase : (k l : Idx) → (a b : G) → Σ[ z ∈ ⊕HIT Idx (λ _ → G) (λ _ → Gstr) ] (base k a add base l b ≡ z)
    cbnBaseBase k l a b with discreteIdx k l
    ... | yes p = (baseBis l ((Gstr + a) b)) ,
                  cong (λ X → X add base l b) (cong (λ X → base X a) p)
                  ∙ base-add _ _ _
                  ∙ base≡baseBis _ _
    ... | no ¬p = (baseBis k a add baseBis l b) , (cong₂ _add_ (base≡baseBis _ _) (base≡baseBis _ _))

    cbnBaseAdd : (k : Idx) → (a : G) → (V U : ⊕HIT Idx (λ _ → G) (λ _ → Gstr))
                 → Σ[ z ∈ ⊕HIT Idx (λ _ → G) (λ _ → Gstr) ] (base k a add (U add V) ≡ z)
    cbnBaseAdd k a V = DS-Ind-Prop.f _ _ _ _ (λ _ → isPropSingl)
                       ((baseBis k a add V) , cong₂ _add_ (base≡baseBis k a) (addComm _ _ ∙ addRid _))
                       (λ l b → helper l b )
                       λ {U} {U'} ind-U ind-U' → (base k a add ((U add U') add V)) , refl

               where
               helper : (l : Idx) → (b : G) → Σ[ z ∈ ⊕HIT Idx (λ _ → G) (λ _ → Gstr) ] (base k a add (base l b add V) ≡ z)
               helper l b with discreteIdx k l
               ... | yes p = (baseBis l (_+_ Gstr a b) add V) ,
                             addAssoc _ _ _
                             ∙ cong (λ X → (base X a add base l b) add V) p
                             ∙ cong (λ X → X add V) (base-add _ _ _)
                             ∙ cong (λ X → X add V) (base≡baseBis _ _)
               ... | no ¬p = ((baseBis k a add (baseBis l b add V))) ,
                             (cong₂ (λ X Y → (X add (Y add V))) (base≡baseBis _ _) (base≡baseBis _ _))

{- * : baseBis could be replace by base
       this would make it faster because less evaluating but
       then it would normlaise less if the user is doing smething wrong -}

  _addBis_ : ⊕HIT Idx (λ _ → G) (λ _ → Gstr) → ⊕HIT Idx (λ _ → G) (λ _ → Gstr) → ⊕HIT Idx (λ _ → G) (λ _ → Gstr)
  _addBis_ x y = fst (Norm0 x y)

  add≡addBis : (x y : ⊕HIT Idx (λ _ → G) (λ _ → Gstr)) → x add y ≡ x addBis y
  add≡addBis x y = snd (Norm0 x y)


  -- AbGroup Properties of addBis
  addBisAssoc : (x y z : ⊕HIT Idx (λ _ → G) (λ _ → Gstr)) → x addBis (y addBis z) ≡ (x addBis y) addBis z
  addBisAssoc x y z = sym (add≡addBis x (y addBis z))
                      ∙ cong (λ X → x add X) (sym (add≡addBis y z))
                      ∙ addAssoc x y z
                      ∙ add≡addBis (x add y) z
                      ∙ cong (λ X → X addBis z) (add≡addBis x y)

  addBisIdR : (x : ⊕HIT Idx (λ _ → G) (λ _ → Gstr)) → x addBis neutral ≡ x
  addBisIdR x = sym (add≡addBis x neutral) ∙ addRid x

  addBisComm : (x y : ⊕HIT Idx (λ _ → G) (λ _ → Gstr)) → x addBis y ≡ y addBis x
  addBisComm x y = sym (add≡addBis x y) ∙ addComm x y ∙ add≡addBis y x


  -- inverse
  invBis : ⊕HIT Idx (λ _ → G) (λ _ → Gstr) → ⊕HIT Idx (λ _ → G) (λ _ → Gstr)
  invBis = DS-Rec-Set.f _ _ _ _ trunc
           neutral
           base
           (λ xs ys → ys addBis xs)
           (λ xs ys zs → sym (addBisAssoc zs ys xs))
           (λ xs → addBisComm neutral xs ∙ addBisIdR xs)
           (λ xs ys → addBisComm ys xs)
           base-neutral
           λ r a b → base-eq r a b

    where
    base-eq : (r : Idx) → (a b : G) → (base r b addBis base r a) ≡ base r ((Gstr + a) b)
    base-eq r a b with discreteIdx r r
    ... | yes p = {!!}
    ... | no ¬p = ⊥.rec (¬p refl)


-- Examples :
module PolynomialExamples where
  open AbGroupStr (snd (⊕HIT-AbGr ℕ(λ _ → ℤ) (λ _ → snd ℤAbGroup)))
  open +BisPol ℕ ℤ (snd ℤAbGroup) discreteℕ discreteℤ
  open Examples baseBis invBis (_addBis_)

  aa = P1'
  bb = P2'
  cc = Q1'
  dd = Q2'
  ee = Q3'
  ff = Q4'

  P1'≡PNorm0 : P1' ≡ PNorm0
  P1'≡PNorm0 = refl

  P2'≡PNorm0 : P2' ≡ PNorm0
  P2'≡PNorm0 = refl

  -- Norm0P1≡PNorm0 : applyNorm0 P1 ≡ PNorm0
  -- Norm0P1≡PNorm0 = refl

  Q3'≡Q2' : Q3' ≡ Q2'
  Q3'≡Q2' = refl

  Q2'≡Q1' : Q2' ≡ Q1'
  Q2'≡Q1' = {!refl!}
  -- error 12 != 17
  -- => this doesn't contract "base"

  -- Q1'≡QNorm0 : Q1' ≡ QNorm0
  -- Q1'≡QNorm0 = {!refl!}
  -- error : base 0 0 add base 2 1 != base 2 1
  -- => doesn't simplify base n 0

  -- U≡neutral : U ≡ neutral
  -- U≡neutral = {!refl!}
  -- Big bug, nothing simplifie exacte the 0

  R' = R
  Rinv' = Rinv
  T' = T
  U' = U

open PolynomialExamples
