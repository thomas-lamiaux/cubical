{-# OPTIONS --safe #-}
module Cubical.UnivParam.RelationEquiv where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path

open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation

open Iso

-- private variable

-----------------------------------------------------------------------------
-- Definition

module UnivRel
  {ℓ : Level}
  where

  Rel : (A B : Type ℓ) → Type (ℓ-suc ℓ)
  Rel A B = A → B → Type ℓ

  symRel : {A B : Type ℓ} → (R : Rel A B) → Rel B A
  symRel R b a = R a b

  Op : {A B : Type ℓ} → (R : Rel A B) → Type ℓ
  Op  {A} {B} R = (a : A) → isContr (Σ[ b ∈ B ] R a b)

  isUnivRel : {A B : Type ℓ} → (R : Rel A B) → Type ℓ
  isUnivRel R = Op R × Op (symRel R)

  isPropOp : {A B : Type ℓ} → (R : Rel A B) → isProp (Op R)
  isPropOp R = isPropΠ (λ x → isPropIsContr)

  isPropUnivRel : {A B : Type ℓ} → (R : Rel A B) → isProp (isUnivRel R)
  isPropUnivRel R = isProp× (isPropOp R) (isPropOp (symRel R))

  _⋈_ : (A B : Type ℓ) → Type (ℓ-suc ℓ)
  _⋈_ A B = Σ[ R ∈ Rel  A B ] isUnivRel R

  sym⋈ : {A B : Type ℓ} → A ⋈ B → B ⋈ A
  sym⋈ (R , Rop , symRop) = (symRel R) , (symRop , Rop)


module UnivRel-Equiv
  {ℓ : Level}
  where

  open UnivRel
  open isHAEquiv

-----------------------------------------------------------------------------
-- Direct sens

  Rel→fun : {A B : Type ℓ} → (Ru : A ⋈ B) → (A → B)
  Rel→fun (R , Rop , symRop) a = fst (fst (Rop a))

  center : {A B : Type ℓ} → (Ru : A ⋈ B) → (a : A) → Ru .fst a (Rel→fun Ru a)
  center {A} {B} (R , Rop , symRop) a = snd (fst (Rop a))

  Rel→inv : {A B : Type ℓ} → (Ru : A ⋈ B) → (B → A)
  Rel→inv Ru = Rel→fun (sym⋈ Ru)

  Rel→sect : {A B : Type ℓ} → (Ru : A ⋈ B) → (b : B) → Rel→fun Ru (Rel→inv Ru b) ≡ b
  Rel→sect (R , Rop , symRop) b = fst (PathPΣ (snd (Rop (Rel→inv Ru b))
                                               (b , center (sym⋈ Ru) b)))
    where
    Ru = R , Rop , symRop

  Rel→retr : {A B : Type ℓ} → (Ru : A ⋈ B) → (a : A) → Rel→inv Ru (Rel→fun Ru a) ≡ a
  Rel→retr Ru a = Rel→sect (sym⋈ Ru) a

  Rel→equiv : (A B : Type ℓ) → (R : A ⋈ B) → (A ≃ B)
  Rel→equiv A B Ru = isoToEquiv is
    where
    is : Iso A B
    fun is = Rel→fun Ru
    inv is = Rel→inv Ru
    rightInv is = Rel→sect Ru
    leftInv is = Rel→retr Ru


-----------------------------------------------------------------------------
-- Converse sens

  Iso→R : {A B : Type ℓ} → (Iso A B) → A → B → Type ℓ
  Iso→R e a b = fun e a ≡ b

  Equiv→Rop : {A B : Type ℓ} → (e : Iso A B ) → Op (Iso→R e)
  Equiv→Rop e a = isContrSingl (fun e a)

  Iso→symRop : {A B : Type ℓ} → (e : Iso A B ) → Op (symRel (Iso→R e))
  Iso→symRop e b = ((inv e b) , (rightInv e b)) , helper
    where
    helper : _
    helper (a , p) = ΣPathTransport→PathΣ _ _
                     (sym (cong (inv e) p) ∙ leftInv e a ,
                     (subst (λ x → fun e x ≡ b) (sym (cong (inv e) p) ∙ leftInv e a) (rightInv e b)
                            ≡⟨ substInPathsfR (fun e) (sym (cong (inv e) p) ∙ leftInv e a) (rightInv e b) ⟩
                     sym (cong (fun e) (sym (cong (inv e) p) ∙ leftInv e a)) ∙ rightInv e b
                             ≡⟨ cong (λ X → sym X ∙ rightInv e b)
                                     (cong-∙ (fun e) (sym (cong (inv e) p)) (leftInv e a)) ⟩
                     sym (cong (fun e) (sym (cong (inv e) p)) ∙ cong (fun e) (leftInv e a)) ∙ rightInv e b
                             ≡⟨ cong (λ X → X ∙ rightInv e b)
                                     (symDistr (cong (fun e) (sym (cong (inv e) p)))
                                     (cong (fun e) (leftInv e a))) ⟩
                     (sym (cong (fun e) (leftInv e a)) ∙ cong ((fun e) ∘ (inv e)) (sym (sym p))) ∙ rightInv e b
                             ≡⟨ cong (λ X → (sym (cong (fun e) (leftInv e a)) ∙ cong ((fun e) ∘ (inv e)) X) ∙ rightInv e b)
                                     (symInvo p) ⟩
                     (sym (cong (fun e) (leftInv e a)) ∙ cong ((fun e) ∘ (inv e)) p) ∙ rightInv e b
                            ≡⟨  cong (λ X → (sym X ∙ cong ((fun e) ∘ (inv e)) p) ∙ rightInv e b)
                                      ((snd (iso→HAEquiv e)) .com a) ⟩
                     {!!}       ≡⟨ {!!} ⟩ -- Plus le meme rightInv !!! => travailler directement avec HAE
                     {!!}       ≡⟨ {!!} ⟩
                     {!!} ∎) )
