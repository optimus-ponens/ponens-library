{-
This module is for operations on two sets.

TODO:
* crossWith : (Key1 → Key2 → Key3) → St1 → St2 → St3
* properties of (map f):
  assume: Congruent f
  g = (map f)⁻¹
  Surjective (map f)
  Injective g
  Injective f → Bijective f
  Surjective g → Bijective g
  Inverseʳ g f -- map f ∘ g = id
* properties of functions on finite sets:
  f : St1 → St2 -- Need to define an arrow for functions between finite sets. Use ⟦_⟧-Keys?
  assume: Congruent f, Surjective f
  ∃ f⁻¹ s.t. f ∘ f⁻¹ = id -- Inverseʳ f⁻¹ f
  Now (f ~ f⁻¹) properties are the same as (map f ~ g)'s properties above.
-}

{-# OPTIONS --with-K --safe #-}

open import Relation.Binary.Bundles using (StrictTotalOrder; DecSetoid; Setoid)

module Ponens.Data.FinSet.Binary
  {a1 ℓ≈1 ℓ<1} (sto1 : StrictTotalOrder a1 ℓ≈1 ℓ<1)
  {a2 ℓ≈2 ℓ<2} (sto2 : StrictTotalOrder a2 ℓ≈2 ℓ<2)
  where

import Data.List as List
import Data.List.Membership.Setoid.Properties as ListMem
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; Σ-syntax)
open import Function using (_∘_; _on_; Inverseˡ)
open import Level using (Level; _⊔_)
open import Ponens.Data.FinSet using (St; ⟦_⟧; ⟦_⟧-Keys; ⟦_⟧-Keys-setoid; toList; ⟦toList⟧; fromList; ⟦fromList⟧; ∈-resp-≈)
open import Ponens.Relation.Binary.Align using (alignStrictTotalOrder)
open import Relation.Binary using (_Preserves_⟶_)
open import Relation.Unary as U using (Pred)

open StrictTotalOrder sto1 using () renaming (Carrier to Key1)
ℓa1 : Level
ℓa1 = a1 ⊔ ℓ≈1 ⊔ ℓ<1
sto1-aligned : StrictTotalOrder a1 ℓa1 ℓa1
sto1-aligned = alignStrictTotalOrder sto1
module Eq1 = StrictTotalOrder.Eq sto1-aligned
open Eq1 using () renaming (setoid to setoid1)
open Setoid setoid1 using () renaming (_≈_ to _≈1_)
import Data.List.Membership.Setoid setoid1 as ListMem1
St1 : Set ℓa1
St1 = St sto1
⟦_⟧1 : St1 → Pred Key1 ℓa1
⟦_⟧1 = ⟦_⟧ sto1
⟦_⟧-Keys1 : St1 → Set ℓa1
⟦_⟧-Keys1 = ⟦_⟧-Keys sto1
⟦_⟧-Keys-setoid1 : St1 → Setoid ℓa1 ℓa1
⟦_⟧-Keys-setoid1 = ⟦_⟧-Keys-setoid sto1

open StrictTotalOrder sto2 using () renaming (Carrier to Key2)
ℓa2 : Level
ℓa2 = a2 ⊔ ℓ≈2 ⊔ ℓ<2
sto2-aligned : StrictTotalOrder a2 ℓa2 ℓa2
sto2-aligned = alignStrictTotalOrder sto2
module Eq2 = StrictTotalOrder.Eq sto2-aligned
open Eq2 using () renaming (setoid to setoid2)
open Setoid setoid2 using () renaming (_≈_ to _≈2_)
import Data.List.Membership.Setoid setoid2 as ListMem2
St2 : Set ℓa2
St2 = St sto2
⟦_⟧2 : St2 → Pred Key2 ℓa2
⟦_⟧2 = ⟦_⟧ sto2
⟦_⟧-Keys2 : St2 → Set ℓa2
⟦_⟧-Keys2 = ⟦_⟧-Keys sto2
⟦_⟧-Keys-setoid2 : St2 → Setoid ℓa2 ℓa2
⟦_⟧-Keys-setoid2 = ⟦_⟧-Keys-setoid sto2

-- TODO: Maybe use (f : setoid1 Function.Bundles.→ₛ setoid2) instead of (f : Key1 → Key2).
--       Then below (f Preserves _≈1_ ⟶ _≈2_) properties might not be needed.
--       This is called `Func` in stdlib.
--       Further, it might be simpler for "Key1" to mean the setoid rather than the carrier.
map : (Key1 → Key2) → St1 → St2
map f = fromList sto2 ∘ List.map f ∘ toList sto1
-- Note that `map` is covariant and Relation.Unary.⊢ is contravariant.
⟦map⟧⁺ : (f : Key1 → Key2) → f Preserves _≈1_ ⟶ _≈2_ → (t : St1) →
         ⟦ t ⟧1 U.⊆ (⟦ map f t ⟧2 ∘ f)
⟦map⟧⁺ f pres t {k1} k1∈t =
  let k1∈list : k1 ListMem1.∈ toList _ t
      k1∈list = proj₂ (⟦toList⟧ _ _) k1∈t
      k2∈list : (f k1) ListMem2.∈ List.map f (toList _ t)
      k2∈list = ListMem.∈-map⁺ setoid1 setoid2 pres k1∈list
      k2∈tree : ⟦ fromList _ (List.map f (toList _ t)) ⟧2 (f k1)
      k2∈tree = (proj₂ (⟦fromList⟧ _ _)) k2∈list
  in k2∈tree
⟦map⟧⁻ : (f : Key1 → Key2) → (t : St1) (k2 : Key2) →
         ⟦ map f t ⟧2 k2 → ∃ λ k1 → ⟦ t ⟧1 k1 × k2 ≈2 f k1
⟦map⟧⁻ f t k2 k2∈tree =
  let k2∈list : k2 ListMem2.∈ (List.map f (toList _ t))
      k2∈list = proj₁ (⟦fromList⟧ _ _) k2∈tree
      k1inlist : ∃ λ k1 → (k1 ListMem1.∈ (toList _ t)) × (k2 ≈2 f k1) -- TODO: "k1∈list" instead of "k1inlist" causes a parse error.
      k1inlist = ListMem.∈-map⁻ setoid1 setoid2 k2∈list
      k1 , k1∈list , eq = k1inlist
  in k1 , proj₁ (⟦toList⟧ _ _) k1∈list , eq
⟦map⟧ : (f : Key1 → Key2) → f Preserves _≈1_ ⟶ _≈2_ → (t : St1) →
        ⟦ map f t ⟧2 U.≐
        (λ k2 → ∃ λ k1 → (⟦ t ⟧1 k1) × (k2 ≈2 f k1))
⟦map⟧ f pres t =
    (λ {k2} → ⟦map⟧⁻ f t k2)
  , (λ{ {k2} (k1 , k1∈t , eq) →
        ∈-resp-≈ _ (Eq2.sym eq) (⟦map⟧⁺ f pres t k1∈t)})
map-f : (f : Key1 → Key2) → (f Preserves _≈1_ ⟶ _≈2_ ) → (t : St1) → ⟦ t ⟧-Keys1 → ⟦ map f t ⟧-Keys2
map-f f pres t (k1 , k1∈t) = f k1 , ⟦map⟧⁺ f pres t k1∈t
map-inv : (f : Key1 → Key2) → (t : St1) → ⟦ map f t ⟧-Keys2 → ⟦ t ⟧-Keys1
map-inv f t (k2 , k2∈tree) =
  let k1 , k1∈t , _ = ⟦map⟧⁻ f t k2 k2∈tree
  in k1 , k1∈t
{-
-- This might be a more natural ⟦map⟧ because map is covariant.
map-f-inv : (f : Key1 → Key2) → (pres : f Preserves _≈1_ ⟶ _≈2_ ) → (t : St1) →
            Inverseˡ (_≈1_ on proj₁) (_≈2_ on proj₁)
                     (map-f f pres t)
                     (map-inv f t)
map-f-inv f pres t1 {k2 , k2∈t2} {k1 , k1∈t1} eq = b1
  where
  b1 : f k1 ≈2 k2
  b1 = {!!}
  b2 : (_≈1_ on proj₁) (k1 , k1∈t1) (map-inv f t1 (k2 , k2∈t2))
  b2 = eq
-}
