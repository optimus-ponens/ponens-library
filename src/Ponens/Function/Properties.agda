{-# OPTIONS --cubical-compatible --safe #-}

module Ponens.Function.Properties where

open import Function using (_∘_; _⇔_; Congruent; Equivalence; mk⇔)
open import Level using (Level)
open import Relation.Binary using (Rel; _Respects_; Symmetric)
open import Relation.Unary using (Pred)

private
  variable
    a p ℓ : Level
    A : Set a
    P : Pred A p

module _ (_≈_ : Rel A ℓ) where
  cong→resp : Congruent _≈_ _⇔_ P → P Respects _≈_
  cong→resp = Equivalence.to ∘_
  resp→cong : Symmetric _≈_ → P Respects _≈_ → Congruent _≈_ _⇔_ P
  resp→cong sym resp x≈y = mk⇔ (resp x≈y) (resp (sym x≈y))
  cong⇔resp : Symmetric _≈_ → Congruent _≈_ _⇔_ P ⇔ P Respects _≈_
  cong⇔resp sym = mk⇔ cong→resp (resp→cong sym)
