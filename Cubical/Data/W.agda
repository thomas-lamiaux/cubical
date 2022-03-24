{-# OPTIONS --cubical --guardedness #-}

open import Cubical.Foundations.Everything
open import Cubical.Data.Unit

module Cubical.Data.W where

private
  variable
    ℓI ℓS ℓP ℓΓ : Level

data W {I : Type ℓI} (S : I → Type ℓS) (P : ∀ i → S i → Type ℓP) (ℑ : ∀ i (s : S i) → P i s → I) :
  (i : I) → Type (ℓ-max ℓI (ℓ-max ℓS ℓP)) where
  node : ∀ {i} → (s : S i) → (subtree : (p : P i s) → W S P ℑ (ℑ i s p)) → W S P ℑ i

module _ {I : Type ℓI} {S : I → Type ℓS} {P : ∀ i → S i → Type ℓP} {ℑ : ∀ i (s : S i) → P i s → I} where
  getShape : ∀ {i} → W S P ℑ i → S i
  getShape (node s subtree) = s

  getSubtree : ∀ {i} → (w : W S P ℑ i) → (p : P i (getShape w)) → W S P ℑ (ℑ i (getShape w) p)
  getSubtree (node s subtree) = subtree

module WPath {I : Type ℓI} {S : I → Type ℓS} {P : ∀ i → S i → Type ℓP} {ℑ : ∀ i (s : S i) → P i s → I} where
  {-private
    variable
      i i' j : I
  -}

  record Cover {ℓΓ : Level} {Γ Γ' : Type ℓΓ} (pΓ : Γ ≡ Γ') {i i'} (pi : PathP (λ α → pΓ α → I) i i')
    (w : ∀ γ → W S P ℑ (i γ)) (w' : ∀ γ → W S P ℑ (i' γ)) : Type (ℓ-max (ℓ-max ℓS (ℓ-suc ℓΓ)) (ℓ-max (ℓ-suc ℓP) ℓI)) where
    coinductive
    constructor cover
    field
      ps : PathP (λ α → ∀ γ → S (pi α γ)) (getShape ∘ w) (getShape ∘ w')
      csubtree : Cover
        (λ α → Σ[ γ ∈ pΓ α ] P (pi α γ) (ps α γ))
        (λ α (γ , p) → ℑ (pi α γ) (ps α γ) p)
        (λ (γ , p) → getSubtree (w γ) p)
        (λ (γ' , p) → getSubtree (w' γ') p)

  Cover0 : ∀ {i i' : I} (pi : i ≡ i') (w : W S P ℑ i) (w' : W S P ℑ i') → Type (ℓ-max (ℓ-max ℓI ℓS) (ℓ-suc ℓP))
  Cover0 pi w w' = Cover (λ _ → Unit) (λ α u → pi α) (λ u → w) (λ u → w')

  reflCode : (Γ : Type ℓΓ) (i : Γ → I) → (w : ∀ γ → W S P ℑ (i γ)) → Cover (λ _ → Γ) refl w w
  Cover.ps (reflCode Γ i w) = refl
  Cover.csubtree (reflCode Γ i w) = reflCode _ _ _

{-
  encode : (pi : i ≡ i') → ∀ w w' → PathP (λ α → W S P ℑ (pi α)) w w' → Cover pi w w'
  encode {i = i} {i' = _} =
              J (λ i' pi → ∀ w w' → PathP (λ α → W S P ℑ (pi α)) w w' → Cover pi w w')
              (λ w _ → J (λ w' pw → Cover refl w w') (reflCode w))

  encodeRefl : ∀ {i} (w : W S P ℑ i) → encode refl w w refl ≡ reflCode w
  encodeRefl {i} w =
    encode refl w w refl
      ≡⟨ funExt⁻ (funExt⁻ (funExt⁻ (JRefl
        (λ i' pi → ∀ w w' → PathP (λ α → W S P ℑ (pi α)) w w' → Cover pi w w')
        λ w _ → J (λ w' pw → Cover refl w w') (reflCode w)
      ) w) w) refl ⟩
    J (λ w' pw → Cover refl w w') (reflCode w) {w} refl
      ≡⟨ JRefl (λ w' pw → Cover refl w w') (reflCode w) ⟩
    reflCode w ∎

  decode : (pi : i ≡ i') → ∀ w w' → Cover pi w w' → PathP (λ α → W S P ℑ (pi α)) w w'
  decode pi (node s subtree) (node s' subtree') (ps , psubtree) α = node (ps α) (psubtree α)

  decodeRefl : ∀ {i} (w : W S P ℑ i) → decode refl w w (reflCode w) ≡ refl
  decodeRefl (node s subtree) = refl

  decodeEncode : (pi : i ≡ i') → ∀ w w' → (pw : PathP (λ α → W S P ℑ (pi α)) w w') → decode pi w w' (encode pi w w' pw) ≡ pw
  decodeEncode {i = i} {i' = _} =
                    J (λ i' pi → ∀ w w' → (pw : PathP (λ α → W S P ℑ (pi α)) w w') → decode pi w w' (encode pi w w' pw) ≡ pw)
                    λ w _ → J (λ w' pw → decode refl w w' (encode refl w w' pw) ≡ pw) (
                      decode refl w w (encode refl w w refl)
                        ≡⟨ cong (decode refl w w) (encodeRefl w) ⟩
                      decode refl w w (reflCode w)
                        ≡⟨ decodeRefl w ⟩
                      refl ∎
                    )
-}
