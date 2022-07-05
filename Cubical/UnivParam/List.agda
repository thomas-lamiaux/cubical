{-# OPTIONS --safe #-}
module Cubical.UnivParam.List where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.List

open import Cubical.UnivParam.Base

private variable
  ℓ : Level

open Iso

{- Notations
   a , l  for elements
   a', l' for copy of the elements
   x, xa, xl for evidence of their relation between elements
-}

Σ-swap : (A B : Type ℓ) → (C : (a : A) → (b : B) → Type ℓ) →
         (Σ[ a ∈ A ] Σ[ b ∈ B ] C a b) ≃ (Σ[ b ∈ B ] Σ[ a ∈ A ] C a b)
Σ-swap A B C = isoToEquiv is
  where
  is : Iso (Σ[ a ∈ A ] Σ[ b ∈ B ] C a b) (Σ[ b ∈ B ] Σ[ a ∈ A ] C a b)
  fun is (a , b , c) = b , (a , c)
  inv is (b , a , c) = a , (b , c)
  rightInv is = λ _ → refl
  leftInv is = λ _ → refl

RL : {A A' : Type ℓ} → (RA : A → A' → Type ℓ) → Rel (List A) (List A')
RL RA []       []        = Unit*
RL RA []      (a' ∷ l')  = ⊥*
RL RA (a ∷ l)  []        = ⊥*
RL RA (a ∷ l) (a' ∷ l')  = Σ[ xa ∈ RA a a' ] RL RA l l'

module _
  {A : Type ℓ}
  {A' : Type ℓ}
  (RAu@(RA , RAstr) : A ⋈ A')
  where

  module _ where
    codeRL : (l : List A) → Type ℓ
    codeRL [] = Unit*
    codeRL (a ∷ l) = Σ[ a' ∈ A' ] Σ[ l' ∈ List A' ] RL RA (a ∷ l) (a' ∷ l')

    codeRL-fun : (l : List A) → Σ[ l' ∈ List A' ] RL RA l l' → codeRL l
    codeRL-fun [] ([] , x) = tt*
    codeRL-fun (a ∷ l) (a' ∷ l' , x) = a' , (l' , x)

    codeRL-inv : (l : List A) → codeRL l → Σ[ l' ∈ List A' ] RL RA l l'
    codeRL-inv [] tt* = [] , tt*
    codeRL-inv (a ∷ l) (a' , l' , x) = (a' ∷ l') , x

    codeRL-retr : (l : List A) → (r : Σ[ l' ∈ List A' ] RL RA l l') → codeRL-inv l (codeRL-fun l r) ≡ r
    codeRL-retr [] ([] , tt*) = refl
    codeRL-retr (a ∷ l) (a' ∷ l' , x) = refl

    codeRL-sect : (l : List A) → (r : codeRL l) → codeRL-fun l (codeRL-inv l r) ≡ r
    codeRL-sect [] t** = refl
    codeRL-sect (a ∷ l) (a' , l' , x) = refl

  equivCode : (l : List A) → (Σ[ l' ∈ List A' ] RL RA l l') ≃ (codeRL l)
  equivCode l = isoToEquiv is
    where
    is : Iso (Σ[ l' ∈ List A' ] RL RA l l') (codeRL l)
    fun is = codeRL-fun l
    inv is = codeRL-inv l
    rightInv is = codeRL-sect l
    leftInv is = codeRL-retr l

  isOpRL : isOp (RL RA)
  isOpRL [] = isOfHLevelRespectEquiv 0
              (invEquiv (equivCode []))
              isContrUnit*
  isOpRL (a ∷ l) = isOfHLevelRespectEquiv 0
                   (invEquiv
                   ((Σ[ l' ∈ List A' ] RL RA (a ∷ l) l')
                        ≃⟨ equivCode (a ∷ l) ⟩
                    (Σ[ a' ∈ A' ] (Σ[ l' ∈ List A' ] (Σ[ xa ∈ RA a a' ] RL RA l l')))
                        ≃⟨ Σ-cong-equiv-snd (λ a' → Σ-swap _ _ _) ⟩
                    (Σ[ a' ∈ A' ] (Σ[ xa ∈ RA a a' ] (Σ[ l' ∈ List A' ] RL RA l l')))
                        ≃⟨ Σ-cong-equiv-snd (λ a' → Σ-contractSnd (λ xa → isOpRL l)) ⟩
                    (Σ[ a' ∈ A' ] RA a a') ■ ))
                   (fst RAstr a)

module _
  {A : Type ℓ}
  {A' : Type ℓ}
  (RAu@(RA , RAstr) : A ⋈ A')
  where

  symRL : (l : List A) → (l' : List A') → symRel (RL RA) l' l ≃ RL (symRel RA) l' l
  symRL []       []       = idEquiv _
  symRL []      (a' ∷ l') = idEquiv _
  symRL (a ∷ l)  []       = idEquiv _
  symRL (a ∷ l) (a' ∷ l') = Σ-cong-equiv-snd (λ a' → symRL l l')

  isOpSymRL : isOp (symRel (RL RA))
  isOpSymRL l' = isOfHLevelRespectEquiv 0
                 (invEquiv (Σ-cong-equiv-snd (λ l → symRL l l')))
                 (isOpRL (sym⋈ RAu) l')


  RL⋈ : List A ⋈ List A'
  RL⋈ = (RL RA) , ((isOpRL RAu) , isOpSymRL)
