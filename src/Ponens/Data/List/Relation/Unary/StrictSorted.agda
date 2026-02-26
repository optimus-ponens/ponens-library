{-
StrictSorted is the strictly sorted property of Lists.
It's equivalent to (Sorted ∩ Unique) but is easier to prove and use in many cases.
-}

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (StrictTotalOrder)

module Ponens.Data.List.Relation.Unary.StrictSorted
  {a ℓ₁ ℓ₂} (sto : StrictTotalOrder a ℓ₁ ℓ₂) where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; _∷_)
open import Data.List.Relation.Unary.All as All using (All; [])
open import Data.List.Relation.Unary.AllPairs as AllPairs using (AllPairs)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.Any.Properties using (¬Any[])
open import Data.List.Relation.Unary.Linked as Linked using (Linked; [-]; _∷_)
open import Data.List.Relation.Unary.Linked.Properties using (Linked⇒All; Linked⇒AllPairs; AllPairs⇒Linked)
open import Data.List.Relation.Unary.Sorted.TotalOrder.Properties using (Sorted⇒AllPairs)
open import Data.Product using (_,_; <_,_>)
open import Data.Sum using (inj₁; inj₂)
open import Function using (flip)
open import Level using (_⊔_)
import Relation.Binary as Binary
open import Relation.Binary.Bundles using (TotalOrder)
import Relation.Binary.Construct.Intersection as Binary
open import Relation.Binary.Structures using (IsTotalOrder)
open import Relation.Unary using (Pred; _∩_; _⊆_; _≐_)

module STO = StrictTotalOrder sto
open STO using (module Eq; _≈_; _<_) renaming (Carrier to A)
open Eq using (setoid; _≉_)
open import Relation.Binary.Construct.StrictToNonStrict _≈_ _<_ as StrictToNonStrict using (_≤_)
isTotalOrder : IsTotalOrder _≈_ _≤_
isTotalOrder = StrictToNonStrict.isTotalOrder STO.isStrictTotalOrder
totalOrder : TotalOrder a ℓ₁ (ℓ₁ ⊔ ℓ₂)
totalOrder = record { isTotalOrder = isTotalOrder }
open import Data.List.Relation.Unary.Sorted.TotalOrder totalOrder using (Sorted)
open import Data.List.Membership.Setoid setoid using (_∈_)
open import Data.List.Relation.Unary.Unique.Setoid setoid using (Unique; []; _∷_)
import Relation.Binary.Reasoning.StrictPartialOrder STO.strictPartialOrder as SPO-Reasoning

≤∧≉⇒< : _≤_ Binary.∩ _≉_ Binary.⇒ _<_
≤∧≉⇒< {x} {y} (inj₁ x<y , x≉y) = x<y
≤∧≉⇒< {x} {y} (inj₂ x≈y , x≉y) = ⊥-elim (x≉y x≈y)

StrictSorted : Pred (List A) (a ⊔ ℓ₂)
StrictSorted xs = Linked _<_ xs

StrictSorted⇒All : ∀ {v x xs} → v < x → StrictSorted (x ∷ xs) → All (v <_) (x ∷ xs)
StrictSorted⇒All = Linked⇒All STO.trans

StrictSorted⇒AllPairs : ∀ {xs} → StrictSorted xs → AllPairs _<_ xs
StrictSorted⇒AllPairs = Linked⇒AllPairs STO.trans

AllPairs⇒StrictSorted : ∀ {xs} → AllPairs _<_ xs → StrictSorted xs
AllPairs⇒StrictSorted = AllPairs⇒Linked

StrictSorted→Sorted : StrictSorted ⊆ Sorted
StrictSorted→Sorted = Linked.map λ x<y → begin _ <⟨ x<y ⟩ _ ∎
  where open SPO-Reasoning

StrictSorted→Unique : StrictSorted ⊆ Unique
StrictSorted→Unique {[]} xs-ss = []
StrictSorted→Unique {x ∷ xs} [-] = [] ∷ []
StrictSorted→Unique {x ∷ xs} (x<y ∷ xs-ss) =
  (All.map (flip STO.irrefl) (StrictSorted⇒All x<y xs-ss))
  AllPairs.∷
  (StrictSorted→Unique xs-ss)

Sorted-Unique→StrictSorted : Sorted ∩ Unique ⊆ StrictSorted
Sorted-Unique→StrictSorted {xs} (xs-s , xs-u) =
  AllPairs⇒StrictSorted (AllPairs.zipWith ≤∧≉⇒< (Sorted⇒AllPairs totalOrder xs-s , xs-u))

StrictSorted≐SortedUnique : StrictSorted ≐ Sorted ∩ Unique
StrictSorted≐SortedUnique =
    < StrictSorted→Sorted , StrictSorted→Unique >
  , Sorted-Unique→StrictSorted

∈→< : {x : A} → {xs : List A} → {y : A} → StrictSorted (x ∷ xs) → y ∈ xs → x < y
∈→< xxs-s y∈xs with StrictSorted⇒AllPairs xxs-s
... | x<xs AllPairs.∷ _ = All.lookupₛ setoid STO.<-respʳ-≈ x<xs y∈xs

∈→≤ : {x : A} → {xs : List A} → {y : A} → StrictSorted (x ∷ xs) → y ∈ (x ∷ xs) → x ≤ y
∈→≤ {x} {xs} {y} xxs-s (here y≈x) =
  begin x ≈⟨ Eq.sym y≈x ⟩ y ∎
  where open SPO-Reasoning
∈→≤ {x} {xs} {y} xxs-s (there y∈xs) =
  begin x <⟨ ∈→< xxs-s y∈xs ⟩ y ∎
  where open SPO-Reasoning

∈∷⊆→∈⊆ : {x y : A} → {xs ys : List A} →
     StrictSorted (x ∷ xs) → StrictSorted (y ∷ ys) →
     (_∈ (x ∷ xs)) ⊆ (_∈ (y ∷ ys)) → (_∈ xs) ⊆ (_∈ ys)
∈∷⊆→∈⊆ {x} {y} xxs-s yys-s xxs→yys {z} z∈xs with xxs→yys (there z∈xs)
... | here z≈y = ⊥-elim (STO.irrefl (Eq.sym z≈y) y<z)
  where
  open SPO-Reasoning
  y<z : y < z
  y<z = begin-strict
    y ≤⟨ ∈→≤ yys-s (xxs→yys (here Eq.refl)) ⟩
    x <⟨ ∈→< xxs-s z∈xs ⟩
    z ∎
... | there z∈ys = z∈ys

∈∷≐→∈≐ : {x y : A} {xs ys : List A} →
            StrictSorted (x ∷ xs) → StrictSorted (y ∷ ys) →
            (_∈ (x ∷ xs)) ≐ (_∈ (y ∷ ys)) → (_∈ xs) ≐ (_∈ ys)
∈∷≐→∈≐ xxs-s yys-s (eq→ , eq←) =
    (∈∷⊆→∈⊆ xxs-s yys-s eq→)
  , (∈∷⊆→∈⊆ yys-s xxs-s eq←)

¬-cross-heads : {x : A} {xs : List A} {y : A} {ys : List A} →
                   StrictSorted (x ∷ xs) → StrictSorted (y ∷ ys) →
                   x ∈ ys → y ∈ xs → ⊥
¬-cross-heads {x} {xs} {y} {ys} xxs-s yys-s x∈ys y∈xs =
  ⊥-elim (STO.asym (∈→< yys-s x∈ys) (∈→< xxs-s y∈xs))

StrictSorted-≐→Pointwise : {xs ys : List A} →
                           StrictSorted xs → StrictSorted ys →
                           (_∈ xs) ≐ (_∈ ys) → Pointwise _≈_ xs ys
StrictSorted-≐→Pointwise {[]} {[]} xs-s ys-s (∈xs→∈ys , ∈ys→∈xs) = Pointwise.[]
StrictSorted-≐→Pointwise {[]} {y ∷ ys} xs-s ys-s (∈xs→∈ys , ∈ys→∈xs) =
  ⊥-elim (¬Any[] (∈ys→∈xs (here Eq.refl)))
StrictSorted-≐→Pointwise {x ∷ xs} {[]} xs-s ys-s (∈xs→∈ys , ∈ys→∈xs) =
  ⊥-elim (¬Any[] (∈xs→∈ys (here Eq.refl)))
StrictSorted-≐→Pointwise {x ∷ xs} {y ∷ ys} xxs-s yys-s (∈xs→∈ys , ∈ys→∈xs) =
  x≈y ∷ xs=ys
  where
  x≈y : x ≈ y
  x≈y with ∈xs→∈ys (here Eq.refl) | ∈ys→∈xs (here Eq.refl)
  ... | here x≈y | _ = x≈y
  ... | there _ | here y≈x = Eq.sym y≈x
  ... | there x∈ys | there y∈xs = ⊥-elim (¬-cross-heads xxs-s yys-s x∈ys y∈xs)
  xs=ys : Pointwise _≈_ xs ys
  xs=ys = StrictSorted-≐→Pointwise (Linked.tail xxs-s) (Linked.tail yys-s)
            (∈∷≐→∈≐ xxs-s yys-s (∈xs→∈ys , ∈ys→∈xs))
