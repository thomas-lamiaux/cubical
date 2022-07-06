{-# OPTIONS --safe #-}
module Cubical.UnivParam.Coproduct where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Sum

open import Cubical.UnivParam.Base

private variable
  ℓ : Level

open Iso

{- Notations
   a , l  for elements
   a', l' for copy of the elements
   x, xa, xl for evidence of their relation between elements
-}

R⊎ : {A A' B B' : Type ℓ} → (RA : Rel A A') → (RB : Rel B B') → Rel (A ⊎ B) (A' ⊎ B')
R⊎ RA RB (inl a) (inl a') = RA a a'
R⊎ RA RB (inl a) (inr b') = ⊥*
R⊎ RA RB (inr b) (inl a') = ⊥*
R⊎ RA RB (inr b) (inr b') = RB b b'

module _
  {A : Type ℓ}
  {A' : Type ℓ}
  (RAu@(RA , RAstr) : A ⋈ A')
  {B : Type ℓ}
  {B' : Type ℓ}
  (RBu@(RB , RBstr) : B ⋈ B')
  where

  module _ where
    codeR⊎ : (x : A ⊎ B) → Type ℓ
    codeR⊎ (inl a) = Σ[ a' ∈ A' ] RA a a'
    codeR⊎ (inr b) = Σ[ b' ∈ B' ] RB b b'

    codeR⊎-fun : (x : A ⊎ B) → Σ[ y ∈ A' ⊎ B' ] R⊎ RA RB x y → codeR⊎ x
    codeR⊎-fun (inl a) (inl a' , r) = a' , r
    codeR⊎-fun (inr b) (inr b' , r) = b' , r

    codeR⊎-inv : (x : A ⊎ B) → codeR⊎ x → Σ[ y ∈ A' ⊎ B' ] R⊎ RA RB x y
    codeR⊎-inv (inl a) (a' , ra) = inl a' , ra
    codeR⊎-inv (inr b) (b' , rb) = inr b' , rb

    codeR⊎-retr : (x : A ⊎ B) → (z : Σ[ y ∈ A' ⊎ B' ] R⊎ RA RB x y) → codeR⊎-inv x (codeR⊎-fun x z) ≡ z
    codeR⊎-retr (inl a) (inl a' , r) = refl
    codeR⊎-retr (inr b) (inr b' , r) = refl

    codeR⊎-sect : (x : A ⊎ B) → (z : codeR⊎ x) → codeR⊎-fun x (codeR⊎-inv x z) ≡ z
    codeR⊎-sect (inl a) (a' , r) = refl
    codeR⊎-sect (inr b) (b' , r) = refl

  equivCode : (x : A ⊎ B) → (Σ[ y ∈ A' ⊎ B' ] R⊎ RA RB x y) ≃ (codeR⊎ x)
  equivCode x = isoToEquiv is
    where
    is : Iso (Σ[ y ∈ A' ⊎ B' ] R⊎ RA RB x y) (codeR⊎ x)
    fun is = codeR⊎-fun x
    inv is = codeR⊎-inv x
    rightInv is = codeR⊎-sect x
    leftInv is = codeR⊎-retr x

  isOpR⊎ : isOp (R⊎ RA RB)
  isOpR⊎ (inl a) = isOfHLevelRespectEquiv 0
                   (invEquiv (equivCode (inl a)))
                   (fst RAstr a)
  isOpR⊎ (inr b) = isOfHLevelRespectEquiv 0
                   (invEquiv (equivCode (inr b)))
                   (fst RBstr b)


module _
  {A : Type ℓ}
  {A' : Type ℓ}
  (RAu@(RA , RAstr) : A ⋈ A')
  {B : Type ℓ}
  {B' : Type ℓ}
  (RBu@(RB , RBstr) : B ⋈ B')
  where

  symR⊎ : (x : A ⊎ B) → (y : A' ⊎ B') → symRel (R⊎ RA RB) y x ≃ R⊎ (symRel RA) (symRel RB) y x
  symR⊎ (inl a) (inl a') = idEquiv _
  symR⊎ (inl a) (inr b') = idEquiv _
  symR⊎ (inr b) (inl a') = idEquiv _
  symR⊎ (inr b) (inr b') = idEquiv _

  isOpSymR⊎ : isOp (symRel (R⊎ RA RB))
  isOpSymR⊎ y = isOfHLevelRespectEquiv 0
                 (invEquiv (Σ-cong-equiv-snd (λ x → symR⊎ x y)))
                 (isOpR⊎ (sym⋈ RAu) (sym⋈ RBu) y)


  R⊎⋈ : (A ⊎ B) ⋈ (A' ⊎ B')
  R⊎⋈ = (R⊎ RA RB) , ((isOpR⊎ RAu RBu) , isOpSymR⊎)
