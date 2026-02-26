{-# OPTIONS --cubical-compatible --safe #-}

module Ponens.Data.Product.Properties where

open import Data.Product using (Σ; proj₁)
open import Function using (_on_)
open import Level using (Level; _⊔_)
open import Relation.Binary using (Rel)
open import Relation.Binary.Bundles using (Setoid)
import Relation.Binary.Construct.On as On
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Unary using (Pred)

private
  variable
    a ℓ : Level
    A : Set a

on-proj₁ : {p : Level} → Rel A ℓ → (P : Pred A p) → Rel (Σ A P) ℓ
on-proj₁ _≈_ _ = _≈_ on proj₁

proj₁-isEquivalence : {p : Level} {_≈_ : Rel A ℓ} → IsEquivalence _≈_ → (P : Pred A p) →
                      IsEquivalence (on-proj₁ _≈_ P)
proj₁-isEquivalence eq _ = On.isEquivalence proj₁ eq

proj₁-setoid : {p : Level} (setoid : Setoid a ℓ) → (P : Setoid.Carrier setoid → Set p) → Setoid (a ⊔ p) ℓ
proj₁-setoid setoid P = On.setoid setoid (proj₁ {B = P})
