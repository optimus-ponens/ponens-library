{-
TODO: Is this module used?
-}

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (Setoid)

module Ponens.Data.Maybe.Membership.Setoid {c ℓ} (S : Setoid c ℓ) where

open import Data.Maybe using (Maybe)
open import Data.Maybe.Relation.Unary.Any using (Any)
open import Level using (Level; _⊔_)
open import Relation.Nullary using (¬_)
open import Relation.Unary using (Pred)

open Setoid S renaming (Carrier to A) using (_≈_)

infix 4 _∈_ _∉_

_∈_ : A → Maybe A → Set (c ⊔ ℓ)
x ∈ xs = Any (x ≈_) xs

_∉_ : A → Maybe A → Set (c ⊔ ℓ)
x ∉ xs = ¬ x ∈ xs

⟦_⟧ : Maybe A → Pred A (c ⊔ ℓ)
⟦_⟧ xs x = x ∈ xs

