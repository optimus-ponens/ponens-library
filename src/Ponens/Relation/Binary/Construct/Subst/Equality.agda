{-
Extension of Relation/Binary/Construct/Subst/Equality.agda to handle StrictTotalOrder.
-}

{-# OPTIONS --cubical-compatible --safe #-}

module Ponens.Relation.Binary.Construct.Subst.Equality where

open import Data.Product using (_,_)
open import Function using (_∘_)
open import Relation.Binary using (Rel; _⇔_; Irreflexive; Tri; Trichotomous)
open import Relation.Binary.Definitions using (_Respects₂_; tri<; tri≈; tri>)
open import Relation.Binary.Structures using (IsStrictTotalOrder; IsStrictPartialOrder)

module _
  {a ℓ₁ ℓ₂} {A : Set a} {≈₁ : Rel A ℓ₁} {≈₂ : Rel A ℓ₂}
  (equiv@(to , from) : ≈₁ ⇔ ≈₂)
  where
  open import Relation.Binary.Construct.Subst.Equality equiv

  module _ {ℓ<} {_<_ : Rel A ℓ<} where
    transportTri : (x y : A) → Tri (x < y) (≈₁ x y) (y < x) → Tri (x < y) (≈₂ x y) (y < x)
    transportTri x y (tri< a ¬b ¬c) = tri< a (¬b ∘ from) ¬c
    transportTri x y (tri≈ ¬a b ¬c) = tri≈ ¬a (to b) ¬c
    transportTri x y (tri> ¬a ¬b c) = tri> ¬a (¬b ∘ from) c

    trichotomous : Trichotomous ≈₁ _<_ → Trichotomous ≈₂ _<_
    trichotomous compare x y = transportTri x y (compare x y)

    irreflexive : Irreflexive ≈₁ _<_ → Irreflexive ≈₂ _<_
    irreflexive = _∘ from

    respects₂ : _<_ Respects₂ ≈₁ → _<_ Respects₂ ≈₂
    respects₂ (r , l) = r ∘ from , l ∘ from

    isStrictPartialOrder : IsStrictPartialOrder ≈₁ _<_ → IsStrictPartialOrder ≈₂ _<_
    isStrictPartialOrder X = record
      { isEquivalence = isEquivalence X.isEquivalence
      ; irrefl = irreflexive X.irrefl
      ; trans = X.trans
      ; <-resp-≈ = respects₂ X.<-resp-≈
      } where module X = IsStrictPartialOrder X

    isStrictTotalOrder : IsStrictTotalOrder ≈₁ _<_ → IsStrictTotalOrder ≈₂ _<_
    isStrictTotalOrder X = record
      { isStrictPartialOrder = isStrictPartialOrder X.isStrictPartialOrder
      ; compare = trichotomous X.compare
      } where module X = IsStrictTotalOrder X
