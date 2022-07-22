{-# OPTIONS --safe #-}
module Cubical.UnivParam.Suspension where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Unit

open import Cubical.HITs.Susp

open Iso

private variable
  ℓ : Level


pack : (A : Type ℓ) → (P : Susp A → Type ℓ) →
       (N* : P north) → (S* : P south) → ((a : A) → PathP (λ i → P (merid a i)) N* S*)
       → (x : Susp A) → P x
pack A P N* S* p north = N*
pack A P N* S* p south = S*
pack A P N* S* p (merid a i) = p a i

module _
  (A : Type ℓ)
  (aa : A)
  (A' : Type ℓ)
  (RA : A → A' → Type ℓ)
  where

  data RΣ : Susp A → Susp A' → Type ℓ where
    N* : RΣ north north
    S* : RΣ south south
    merid* : (a : A) → (a' : A') → RA a a' → PathP (λ i → RΣ (merid a i) (merid a' i)) N* S*

  module _
    (P     : {a : Susp A} → {a' : Susp A'} → (RΣ a a' → Type ℓ))
    (Pprop : {a : Susp A} → {a' : Susp A'} → (x : RΣ a a') → isProp (P x))
    (NN*   : P N*)
    (SS*   : P S*)
    where

    code : (x : Susp A) → Type ℓ
    code north = Unit*
    code south = Unit*
    code (merid a i) = Unit*

    fct : (x : Susp A) → (Σ[ y ∈ Susp A' ] RΣ x y) → (code x)
    fct north = λ _ → tt*
    fct south = λ _ → tt*
    fct (merid a i) = λ _ → tt*

    invct : (x : Susp A) → (code x) → (Σ[ y ∈ Susp A' ] RΣ x y)
    invct north = λ _ → north , N*
    invct south = λ _ → south , S*
    invct (merid a i) = {!λ _ → ?!}

    eqSum : (x : Susp A) → Iso (Σ[ y ∈ Susp A' ] RΣ x y) (code x)
    fun (eqSum x) = {!!}
    inv (eqSum x) = {!!}
    rightInv (eqSum x) = {!!}
    leftInv (eqSum x) = {!!}

    isFun : (x : Susp A) → isContr (Σ[ y ∈ Susp A' ] RΣ x y)
    isFun = suspToPropElim aa (λ _ → isPropIsContr) {!!}
