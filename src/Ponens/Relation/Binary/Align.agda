{-
Align the universe levels of properties in bundles.
This enables use of libraries that require homogenous levels,
e.g. equational reasoning for ≐, Unary.Properties, Relation.Unary.Algebra.
-}

{-# OPTIONS --cubical-compatible --safe #-}

module Ponens.Relation.Binary.Align where

open import Data.Product using (_,_)
open import Function using (_∘_)
open import Level using (Level; _⊔_; Lift; lift)
open Lift using (lower)
open import Relation.Binary using (Rel; IsEquivalence; Irreflexive; Transitive; Tri; Trichotomous)
open import Relation.Binary.Bundles using (StrictTotalOrder)
open import Relation.Binary.Definitions using (_Respects₂_; tri<; tri≈; tri>)
open import Relation.Binary.Structures using (IsStrictTotalOrder; IsStrictPartialOrder)

Lift-Rel : ∀ {c ℓ} → (ℓ-other : Level) → {C : Set c} → Rel C ℓ → Rel C (ℓ-other ⊔ ℓ)
Lift-Rel ℓ-other _~_ x y = Lift ℓ-other (x ~ y)

Lift-Tri : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} (ℓa ℓb ℓc : Level) → Tri A B C → Tri (Lift ℓa A) (Lift ℓb B) (Lift ℓc C)
Lift-Tri ℓa ℓb ℓc (tri< a ¬b ¬c) = tri< (lift a) (¬b ∘ lower) (¬c ∘ lower)
Lift-Tri ℓa ℓb ℓc (tri≈ ¬a b ¬c) = tri≈ (¬a ∘ lower) (lift b) (¬c ∘ lower)
Lift-Tri ℓa ℓb ℓc (tri> ¬a ¬b c) = tri> (¬a ∘ lower) (¬b ∘ lower) (lift c)

alignTrichotomous : ∀ {c ℓ₁ ℓ₂} → {C : Set c} → {_≈_ : Rel C ℓ₁} → {_<_ : Rel C ℓ₂} → Trichotomous _≈_ _<_ → Trichotomous (Lift-Rel (c ⊔ ℓ₂) _≈_) (Lift-Rel (c ⊔ ℓ₁) _<_)
alignTrichotomous {c} {ℓ₁} {ℓ₂} compare x y =
  Lift-Tri (c ⊔ ℓ₁) (c ⊔ ℓ₂) (c ⊔ ℓ₁) (compare x y)

Lift-IsEquivalence : ∀ {c ℓ₁} {C : Set c} {_≈_ : Rel C ℓ₁} → (ℓ-lift : Level) → IsEquivalence _≈_ → IsEquivalence (Lift-Rel ℓ-lift _≈_)
Lift-IsEquivalence ℓ-lift record { refl = refl ; sym = sym ; trans = trans } =
  record { refl = λ {_} → lift refl
         ; sym = λ {_} {_} → lift ∘ sym ∘ lower
         ; trans = λ {_} {_} {_} xy yz → lift (trans (lower xy) (lower yz)) }

alignIrreflexive : ∀ {c ℓ₁ ℓ₂} → {C : Set c} {_≈_ : Rel C ℓ₁} {_<_ : Rel C ℓ₂} → Irreflexive _≈_ _<_ → Irreflexive (Lift-Rel (c ⊔ ℓ₂) _≈_) (Lift-Rel (c ⊔ ℓ₁) _<_)
alignIrreflexive {c} {ℓ₁} {ℓ₂} {C} {_≈_} {_<_} irr _≈ℓ_ _<ℓ_ = irr (lower _≈ℓ_) (lower _<ℓ_)

Lift-Transitive : ∀ {c ℓ₂} → {C : Set c} {_<_ : Rel C ℓ₂} (ℓ-lift : Level) → Transitive _<_ → Transitive (Lift-Rel ℓ-lift _<_)
Lift-Transitive ℓ-lift trans xy yz = lift (trans (lower xy) (lower yz))

alignRespects₂ : ∀ {c ℓ₁ ℓ₂} → {C : Set c} {_≈_ : Rel C ℓ₁} {_<_ : Rel C ℓ₂} → _<_ Respects₂ _≈_ → Lift-Rel (c ⊔ ℓ₁) _<_ Respects₂ Lift-Rel (c ⊔ ℓ₂) _≈_
alignRespects₂ (respˡ , respʳ) = (λ _≈ℓ_ _<ℓ_ → lift (respˡ (lower _≈ℓ_) (lower _<ℓ_)))
                               , (λ _≈ℓ_ _<ℓ_ → lift (respʳ (lower _≈ℓ_) (lower _<ℓ_)))

alignIsStrictPartialOrder : ∀ {c ℓ₁ ℓ₂} → {C : Set c} {_≈_ : Rel C ℓ₁} {_<_ : Rel C ℓ₂} → IsStrictPartialOrder _≈_ _<_ → IsStrictPartialOrder (Lift-Rel (c ⊔ ℓ₂) _≈_) (Lift-Rel (c ⊔ ℓ₁) _<_)
alignIsStrictPartialOrder {c} {ℓ₁} {ℓ₂} {C} {_≈_} {_<_} record { isEquivalence = isEquivalence
                                 ; irrefl = irrefl
                                 ; trans = trans
                                 ; <-resp-≈ = <-resp-≈ } =
  record { isEquivalence = Lift-IsEquivalence (c ⊔ ℓ₂) isEquivalence
         ; irrefl = alignIrreflexive {_≈_ = _≈_} irrefl
         ; trans = Lift-Transitive {_<_ = _<_} (c ⊔ ℓ₁) trans
         ; <-resp-≈ = alignRespects₂ <-resp-≈ }

alignIsStrictTotalOrder : ∀ {c ℓ₁ ℓ₂} → {C : Set c} → {_≈_ : Rel C ℓ₁} → {_<_ : Rel C ℓ₂} → IsStrictTotalOrder _≈_ _<_ → IsStrictTotalOrder (Lift-Rel (c ⊔ ℓ₂) _≈_) (Lift-Rel (c ⊔ ℓ₁) _<_)
alignIsStrictTotalOrder record { isStrictPartialOrder = isStrictPartialOrder
                               ; compare = compare } =
  record { isStrictPartialOrder = alignIsStrictPartialOrder isStrictPartialOrder
         ; compare = alignTrichotomous compare }

alignStrictTotalOrder : ∀ {c ℓ₁ ℓ₂} → StrictTotalOrder c ℓ₁ ℓ₂ → StrictTotalOrder c (c ⊔ ℓ₁ ⊔ ℓ₂) (c ⊔ ℓ₁ ⊔ ℓ₂)
alignStrictTotalOrder {c} {ℓ₁} {ℓ₂} record { Carrier = Carrier
                             ; _≈_ = _≈_
                             ; _<_ = _<_
                             ; isStrictTotalOrder = isStrictTotalOrder } =
  record { Carrier = Carrier
         ; _≈_ = Lift-Rel (c ⊔ ℓ₂) _≈_
         ; _<_ = Lift-Rel (c ⊔ ℓ₁) _<_
         ; isStrictTotalOrder = alignIsStrictTotalOrder isStrictTotalOrder }
