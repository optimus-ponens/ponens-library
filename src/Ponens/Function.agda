{-# OPTIONS --cubical-compatible --safe #-}

module Ponens.Function where

open import Data.Product using (_,_)
open import Function using (_∘_; _⇔_; _↔_; Congruent; Equivalence; mk↔; mk⇔)
open import Level using (Level)
open import Relation.Binary using (Rel; _Respects_; Symmetric)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

private
  variable
    a b : Level
    A : Set a
    B : Set b

-- PLFA style
-- TODO: See Function.Definitions.StrictlyInverseˡ
--       Functions here are the same form, so look for something like mk↔-strictly
mk↔-∘ : (f : A → B) (g : B → A) →
        ((x : A) → g (f x) ≡ x) → ((y : B) → f (g y) ≡ y) →
        A ↔ B
mk↔-∘ f g g∘f f∘g = mk↔ {to = f} {from = g} (g∘f' , f∘g')
  where
  g∘f' : ∀ {x y} → y ≡ g x → f y ≡ x
  g∘f' {x} {y} refl = f∘g x
  f∘g' : ∀ {x y} → x ≡ f y → g x ≡ y
  f∘g' {x} {y} refl = g∘f y

module _ {ℓ₁ ℓ₂ : Level} (_≈_ : Rel A ℓ₁) {P : A → Set ℓ₂} where
  cong→resp : Congruent _≈_ _⇔_ P → P Respects _≈_
  cong→resp = Equivalence.to ∘_
  resp→cong : Symmetric _≈_ → P Respects _≈_ → Congruent _≈_ _⇔_ P
  resp→cong sym resp x≈y = mk⇔ (resp x≈y) (resp (sym x≈y))
  cong⇔resp : Symmetric _≈_ → Congruent _≈_ _⇔_ P ⇔ P Respects _≈_
  cong⇔resp sym = mk⇔ cong→resp (resp→cong sym)
