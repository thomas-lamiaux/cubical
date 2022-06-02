{-# OPTIONS --safe #-}
module Cubical.Algebra.DirectSum.tryDS where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat renaming (_+_ to _+n_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma

open import Cubical.Relation.Nullary

open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group.Properties

open import Cubical.HITs.SetQuotients as SQ

private variable
  ℓ : Level

open AbGroupStr
open GroupTheory

module _
  (G : (n : ℕ) → Type ℓ)
  (Gstr : (n : ℕ) → AbGroupStr (G n))
  where


-----------------------------------------------------------------------------------
-- Definition

  ADS : Type ℓ
  ADS = Σ[ f ∈ ((n : ℕ) → G n) ] Σ[ k ∈ ℕ ] ((n : ℕ) → (k < n) → f n ≡ 0g (Gstr n) )

  Rads : ADS → ADS → Type ℓ
  Rads (f , k , x) (g , l , y) = f ≡ g

  DS : Type ℓ
  DS = ADS / Rads

  <-+k-trans : {m k n : ℕ} → (m +n k < n) → m < n
  <-+k-trans {m} {k} {n} p = ≤<-trans (k , +-comm k m) p

  <-k+-trans : {m k n : ℕ} → (k +n m < n) → m < n
  <-k+-trans {m} {k} {n} p = ≤<-trans (k , refl) p


-----------------------------------------------------------------------------------
-- Group Op

  -- 0
  0ADS : ADS
  0ADS = ((λ n → 0g (Gstr n)) , (0 , (λ n r → refl)))

  0DS : DS
  0DS = [ 0ADS ]

  -- Inverse
  -ADS : ADS → ADS
  -ADS (f , k , x) = (λ n → Gstr n .-_ (f n))
                       , (k
                       , (λ n r → cong (- (Gstr n)) (x n r) ∙ inv1g (AbGroup→Group ((G n) , (Gstr n)))))


  -ADSQ : ADS → DS
  -ADSQ x = [ -ADS x ]

  Req-AD : (a b : ADS) → Rads a b → -ADSQ a ≡ -ADSQ b
  Req-AD (f , k , x) (f' , k' , x') p =
         eq/ (-ADS (f , (k , x)))
             (-ADS (f' , (k' , x')))
             (funExt (λ n → cong (- (Gstr n)) (funExt⁻ p n)))

  -DS : DS → DS
  -DS = SQ.rec squash/ -ADSQ Req-AD


  -- Addition
  _+ADS_ : ADS → ADS → ADS
  _+ADS_ (f , k , x) (g , l , y) = ((λ n → _+_ (Gstr n) (f n) (g n))
                                   , (k +n l
                                   , λ n r → cong₂ (_+_ (Gstr n))
                                                    (x n (<-+k-trans r))
                                                    (y n (<-k+-trans r))
                                              ∙ rid (Gstr n) _ ))

  _+ADSQ_ : ADS → ADS → DS
  _+ADSQ_ x y = [ x +ADS y ]

  coLeft : (a b c : ADS) → Rads a b → (a +ADSQ c) ≡ (b +ADSQ c)
  coLeft (f , k , x) (f' , k' , x') (g , l , y) p =
         eq/ ((f , (k , x)) +ADS (g , l , y))
             ((f' , (k' , x')) +ADS (g , (l , y)))
             (funExt (λ n → cong (λ X → (Gstr n) ._+_ X (g n)) (funExt⁻ p n)))

  coRight : (a b c : ADS) → Rads b c → (a +ADSQ b) ≡ (a +ADSQ c)
  coRight (f , k , x) (g , l , y) (g' , l' , y') p =
          eq/ ((f , (k , x)) +ADS (g , l , y))
              ((f , (k , x)) +ADS (g' , (l' , y')))
              (funExt (λ n → cong (λ X → (Gstr n) ._+_ (f n) X) (funExt⁻ p n)))

  _+DS_ : DS → DS → DS
  _+DS_ = SQ.rec2 squash/ _+ADSQ_ coLeft coRight



-----------------------------------------------------------------------------------
-- Properties +

  +DSIdR : (x : DS) → x +DS 0DS ≡ x
  +DSIdR = SQ.elimProp (λ _ → squash/ _ _)
                    (λ { (f , l , x) → eq/ ((f , (l , x)) +ADS 0ADS)
                                            (f , (l , x))
                                            (funExt (λ n → rid (Gstr n) (f n))) })

  -- etc...

-----------------------------------------------------------------------------------
-- Cup Product

  module _
    (_⌣_ : {n m : ℕ} → G n → G m → G (n +n m))
    where

    δgenF : (n : ℕ) → (a : G n) → (k : ℕ) → (G k)
    δgenF n a k with discreteℕ n k
    ... | yes p = subst G p a
    ... | no ¬p = 0g (Gstr k)

    δgenADS : (n : ℕ) → (a : G n) → ADS
    δgenADS n a = (δgenF n a) , (n , helper)
      where
      helper : _
      helper k r with discreteℕ n k
      ... | yes p = ⊥.rec (<→≢ r p)
      ... | no ¬p = refl

    δgen : (n : ℕ) → (a : G n) → DS
    δgen n a = [ δgenADS n a ]

    sumADS : {A : Type ℓ} → (_+A_ : A → A → A) → (ℕ → A) → (k : ℕ) → A
    sumADS _+A_ f zero = f 0
    sumADS _+A_ f (suc k) = (f (suc k)) +A (sumADS _+A_ f k)

    sumADS2 : {A : Type ℓ} → (_+A_ : A → A → A) → (ℕ → ℕ → A) → (k l : ℕ) → A
    sumADS2 _+A_ F k l = sumADS _+A_ (λ i → sumADS _+A_ (λ j → F i j) l) k

    _cupADS_ : ADS → ADS → ADS
    _cupADS_ (f , k , x) (g , l , y) = sumADS2 _+ADS_ (λ i j → δgenADS (i +n j) ((f i) ⌣ (g j))) k l

    _cupADSQ_ : ADS → ADS → DS
    _cupADSQ_ x y = [ x cupADS y ]


    -- some lemma to extend on both side
    coCupL : (a b c : ADS) → Rads a b → (a cupADSQ c) ≡ (b cupADSQ c)
    coCupL (f , k , x) (f' , k' , x') (g , l , y) p =
           eq/ ((f , (k , x)) cupADS (g , (l , y)))
               ((f' , (k' , x')) cupADS (g , (l , y)))
               (sumADS2 _+ADS_ (λ i j → δgenADS (i +n j)  ((f i) ⌣ (g j)))  k        l .fst ≡⟨ {!-- extend!} ⟩
                sumADS2 _+ADS_ (λ i j → δgenADS (i +n j)  ((f i) ⌣ (g j))) (k +n k') l .fst
                        ≡⟨ cong (λ X → sumADS2 _+ADS_ X (k +n k') l .fst)
                                (funExt (λ i → funExt (λ j → cong (λ X → δgenADS (i +n j)  ((X i) ⌣ (g j))) p) )) ⟩
                sumADS2 _+ADS_ (λ i j → δgenADS (i +n j) ((f' i) ⌣ (g j))) (k +n k') l .fst ≡⟨ {!-- extend!} ⟩
                sumADS2 _+ADS_ (λ i j → δgenADS (i +n j) ((f' i) ⌣ (g j)))  k'       l .fst ∎)

    coCupR : (a b c : ADS) → Rads b c → (a cupADSQ b) ≡ (a cupADSQ c)
    coCupR = {!!}

    _cup_ : DS → DS → DS
    _cup_ = SQ.rec2 squash/ _cupADSQ_ coCupL coCupR

-----------------------------------------------------------------------------------
-- Properties of the cup product

    cupAssoc : (x y z : DS) →  x cup (y cup z) ≡ ((x cup y) cup z)
    cupAssoc = elimProp3 (λ _ _ _ → squash/ _ _)
               λ {(f , k , x) (g , l , y) (h , r , z) →
                 eq/ ((f , (k , x)) cupADS ((g , (l , y)) cupADS (h , (r , z))))
                     (((f , (k , x)) cupADS (g , (l , y))) cupADS (h , (r , z)))
                      (fst (sumADS2 _+ADS_ (λ i j → δgenADS (i +n j) ((f i) ⌣ (fst (sumADS2 _+ADS_ (λ m n → δgenADS (m +n n ) (g m ⌣ h n) ) l r) j))) k
                      (fst (snd ((g , (l , y)) cupADS (h , (r , z))))))
                            ≡⟨ {!!} ⟩
                       {!!} ≡⟨ {!!} ⟩
                       {!!} ≡⟨ {!!} ⟩
                       {!!} ∎)}

   -- replace that with a sum 3 ?
   -- done ?
