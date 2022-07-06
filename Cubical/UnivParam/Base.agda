{-# OPTIONS --safe #-}
module Cubical.UnivParam.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

private variable
  ℓ : Level


Rel : (A B : Type ℓ) → Type (ℓ-suc ℓ)
Rel {ℓ = ℓ} A B = A → B → Type ℓ

symRel : {A B : Type ℓ} → (R : Rel A B) → Rel B A
symRel R b a = R a b

isOp : {A B : Type ℓ} → (R : Rel A B) → Type ℓ
isOp {A = A} {B = B} R = (a : A) → isContr (Σ[ b ∈ B ] R a b)

isPropIsOp : {A B : Type ℓ} → (R : Rel A B) → isProp (isOp R)
isPropIsOp R = isPropΠ (λ x → isPropIsContr)

isUnivRel : {A B : Type ℓ} → (R : Rel A B) → Type ℓ
isUnivRel R = isOp R × isOp (symRel R)

isPropIsUnivRel : {A B : Type ℓ} → (R : Rel A B) → isProp (isUnivRel R)
isPropIsUnivRel R = isProp× (isPropIsOp R) (isPropIsOp (symRel R))

_⋈_ : (A B : Type ℓ) → Type (ℓ-suc ℓ)
_⋈_ A B = Σ[ R ∈ Rel  A B ] isUnivRel R

sym⋈ : {A B : Type ℓ} → A ⋈ B → B ⋈ A
sym⋈ (R , Rop , symRop) = (symRel R) , (symRop , Rop)

open Iso

Σ-swap : (A B : Type ℓ) → (C : (a : A) → (b : B) → Type ℓ) →
         (Σ[ a ∈ A ] Σ[ b ∈ B ] C a b) ≃ (Σ[ b ∈ B ] Σ[ a ∈ A ] C a b)
Σ-swap A B C = isoToEquiv is
  where
  is : Iso (Σ[ a ∈ A ] Σ[ b ∈ B ] C a b) (Σ[ b ∈ B ] Σ[ a ∈ A ] C a b)
  fun is (a , b , c) = b , (a , c)
  inv is (b , a , c) = a , (b , c)
  rightInv is = λ _ → refl
  leftInv is = λ _ → refl
