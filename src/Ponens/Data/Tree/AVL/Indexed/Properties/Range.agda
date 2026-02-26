{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (StrictTotalOrder)

module Ponens.Data.Tree.AVL.Indexed.Properties.Range
  {a ℓ₁ ℓ₂} (sto : StrictTotalOrder a ℓ₁ ℓ₂) where

open import Data.Product as × using (_×_; _,_)
open import Data.Sum using (inj₁)
open import Function using (flip)
open import Level using (Level; _⊔_)
open import Ponens.Relation.Unary.Properties using (ℓ-∩-congˡ; Universal→≐)
open import Relation.Binary using (_Respects_)
open import Relation.Binary.Bundles using (DecTotalOrder)
open import Relation.Binary.Structures using (IsStrictTotalOrder; IsDecTotalOrder)
open import Relation.Nullary.Decidable using (_×-dec_)
open import Relation.Unary using (Pred; Decidable; _≐_)
open import Relation.Unary.Algebra using (∩-identityˡ)
open import Relation.Unary.Polymorphic.Properties using (U-Universal)
open import Relation.Unary.Properties using (≐-trans)

open import Data.Tree.AVL.Indexed sto using (Tree; leaf; node; Value; K&_; key; Key⁺; [_]; _<⁺_; _<_<_; ⊥⁺; ⊥⁺<[_]; [_]ᴱ; ordered; trans⁺) renaming (strictTotalOrder to sto⁺)
open import Data.Tree.AVL.Indexed.Relation.Unary.All sto as All using (All; leaf; node)

module STO = StrictTotalOrder sto
open STO using (_≈_) renaming (Carrier to Key)
module STO⁺ = StrictTotalOrder sto⁺
module IsSTO⁺ = IsStrictTotalOrder STO⁺.isStrictTotalOrder
open import Relation.Binary.Construct.StrictToNonStrict STO⁺._≈_ STO⁺._<_ as StrictToNonStrict⁺ using () renaming (_≤_ to _≤⁺_)
isDTO⁺ : IsDecTotalOrder STO⁺._≈_ _≤⁺_
isDTO⁺ = StrictToNonStrict⁺.isDecTotalOrder STO⁺.isStrictTotalOrder
DTO⁺ : DecTotalOrder a (a ⊔ ℓ₁) (a ⊔ ℓ₁ ⊔ ℓ₂)
DTO⁺ = record { isDecTotalOrder = isDTO⁺ }
module DTO⁺ = DecTotalOrder DTO⁺

private
  variable
    v : Level
    V : Value v

bounds-resp-≈ : {l u : Key⁺} → {x x' : Key} → x ≈ x' → l < x < u → l < x' < u
bounds-resp-≈ {l} {u} {x} {x'} eq (l<x , x<u) =
    STO⁺.<-respʳ-≈ [ eq ]ᴱ l<x
  , STO⁺.<-respˡ-≈ [ eq ]ᴱ x<u

∈-ex-ex : Key⁺ → Key⁺ → Pred Key (a ⊔ ℓ₂)
∈-ex-ex lo hi k = lo < k < hi
∈-ex-ex? : (lo hi : Key⁺) → Decidable (∈-ex-ex lo hi)
∈-ex-ex? lo hi k = (lo IsSTO⁺.<? [ k ]) ×-dec ([ k ] IsSTO⁺.<? hi)
∈-ex-ex-resp : (lo hi : Key⁺) → (∈-ex-ex lo hi) Respects _≈_
∈-ex-ex-resp lo hi = bounds-resp-≈

∈-inc-ex : Key⁺ → Key⁺ → Pred Key (a ⊔ ℓ₁ ⊔ ℓ₂)
∈-inc-ex lo hi k = lo ≤⁺ [ k ] × [ k ] <⁺ hi
∈-inc-ex? : (lo hi : Key⁺) → Decidable (∈-inc-ex lo hi)
∈-inc-ex? lo hi k = lo DTO⁺.≤? [ k ] ×-dec ([ k ] IsSTO⁺.<? hi)
∈-inc-ex-resp : (lo hi : Key⁺) → (∈-inc-ex lo hi) Respects _≈_
∈-inc-ex-resp lo hi eq (lo≤x , x<hi) =
    DTO⁺.≤-respʳ-≈ [ eq ]ᴱ lo≤x
  , STO⁺.<-respˡ-≈ [ eq ]ᴱ x<hi

∈-inc-ex-⊥ : (hi : Key⁺) → ∈-inc-ex ⊥⁺ hi ≐ λ k → [ k ] <⁺ hi
∈-inc-ex-⊥ hi =
   ≐-trans (ℓ-∩-congˡ (Universal→≐ (λ k → inj₁ ⊥⁺<[ k ]) U-Universal))
           (∩-identityˡ λ k → [ k ] <⁺ hi)

All-bounded : ∀ {l u h} → (t : Tree V l u h) → All (λ kv → l < key kv < u) t
All-bounded (leaf l<u) = leaf
All-bounded {l = l} {u} {h} (node kv lk ku bal) =
  node
    (ordered lk , ordered ku)
    (All.map (×.map₂ (flip (trans⁺ _) (ordered ku))) (All-bounded lk))
    (All.map (×.map₁ (trans⁺ _ (ordered lk))) (All-bounded ku))
