{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (Setoid)

module Ponens.Data.List.Membership.Setoid.Properties
  {c ℓ} (setoid : Setoid c ℓ)
  where

open import Data.List using (List; filter)
open import Data.List.Relation.Binary.Pointwise as Pointwise using (Pointwise; Any-resp-Pointwise)
open import Data.List.Relation.Unary.All using (All; _∷_)
open import Data.List.Relation.Unary.All.Properties using (all-filter)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.Any.Properties using (lookup-index; filter⁻; filter⁺)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Function using (flip)
open import Relation.Binary.Definitions using (_Respects_)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Nullary using (contradiction)
open import Relation.Unary using (Pred; Decidable; _≐_; _∩_)

open Setoid setoid renaming (Carrier to A) using (isEquivalence; _≈_)
open import Data.List.Membership.Setoid setoid using (_∈_)
module Eq = IsEquivalence isEquivalence

All×∈→P : ∀ {p} → {P : Pred A p} → (P? : Decidable P) → P Respects _≈_ →
     {xs : List A} → {x : A} →
     All P xs → x ∈ xs → P x
All×∈→P P? resp (Px ∷ _) (here x≈) = resp (Eq.sym x≈) Px
All×∈→P P? resp (_ ∷ Ps) (there x∈xs) = All×∈→P P? resp Ps x∈xs

filter⇔∩ : ∀ {p} → {P : Pred A p} → (P? : Decidable P) → P Respects _≈_ →
           (xs : List A) →
           (_∈ filter P? xs) ≐ ((_∈ xs) ∩ P)
filter⇔∩ {P = P} P? resp xs = to , from
   where
   to : {x : A} → (_∈ filter P? xs) x → ((_∈ xs) ∩ P) x
   to {x} x∈ys = filter⁻ P? x∈ys
          , All×∈→P P? resp (all-filter P? xs) x∈ys
   from : {x : A} → ((_∈ xs) ∩ P) x → (_∈ filter P? xs) x
   from {x = x} (x∈xs , Px) with filter⁺ P? x∈xs
   ... | inj₁ x∈ys = x∈ys
   ... | inj₂ ¬Ppath = contradiction (resp (lookup-index x∈xs) Px) ¬Ppath

module PointwiseSetoid = Setoid (Pointwise.setoid setoid)
∈-Respects-Pointwise≈ : (x : A) → (x ∈_) Respects Pointwise _≈_
∈-Respects-Pointwise≈ x = Any-resp-Pointwise {P = x ≈_} (flip Eq.trans)
Pointwise→∈→ : {xs ys : List A} → Pointwise _≈_ xs ys → {x : A} → x ∈ xs → x ∈ ys
Pointwise→∈→ eq {x} x∈xs = ∈-Respects-Pointwise≈ x eq x∈xs
Pointwise→∈ : {xs ys : List A} → Pointwise _≈_ xs ys → (_∈ xs) ≐ (_∈ ys)
Pointwise→∈ eq = (Pointwise→∈→ eq) , Pointwise→∈→ (PointwiseSetoid.sym eq)
