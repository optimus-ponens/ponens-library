{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (StrictTotalOrder)

module Ponens.Data.Tree.AVL.Indexed.Properties.All
  {a ℓ₁ ℓ₂} (sto : StrictTotalOrder a ℓ₁ ℓ₂) where

import Data.List.Relation.Unary.All.Properties as List
open import Function using (_∘_; _⇔_; mk⇔)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)
open import Relation.Unary using (Pred; Decidable)

open import Data.Tree.AVL.Indexed sto using (Tree; leaf; node; Value; K&_; toList)
open import Data.Tree.AVL.Indexed.Relation.Unary.All sto as All using (All; leaf; node)
open import Data.Tree.AVL.Indexed.Relation.Unary.Any sto as Any using (Any; here; left; right)
open import Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties sto using (lookup-result; lookup-rebuild)
open import Ponens.Data.Tree.AVL.Indexed.Properties.ToList sto using (toList⁻; toList⁺; toList-All⁻; toList-All⁺)

module STO = StrictTotalOrder sto
open STO using () renaming (Carrier to Key)

private
  variable
    v p q : Level
    V : Value v
    P : Pred (K& V) p
    Q : Pred (K& V) q

Any×All : ∀ {l u h} {t : Tree V l u h} (path : Any P t) →
          All Q t → Q (Any.lookup path)
Any×All (here p) (node qk qlk qku) = qk
Any×All (left p) (node qk qlk qku) = Any×All p qlk
Any×All (right p) (node qk qlk qku) = Any×All p qku

Any×All-∈ : ∀ {l u h} {t : Tree V l u h} {kv : K& V} →
            Any (kv ≡_) t → All P t → P kv
Any×All-∈ {P = P} {kv = kv} q p rewrite lookup-result q = Any×All q p

All-Any : ∀ {l u h} (t : Tree V l u h) →
          All (λ kv → Any (kv ≡_) t) t
All-Any (leaf l<u) = leaf
All-Any (node kv lk ku bal) =
  node (here refl)
       (All.map (λ z → left z) (All-Any lk))
       (All.map (λ z → right z) (All-Any ku))

-- De Morgan's Laws for All and Any.

¬Any⇒All¬ : ∀ {l u h} {t : Tree V l u h} →
            ¬ Any P t → All (¬_ ∘ P) t
¬Any⇒All¬ {t = t} ¬p =
  toList-All⁻ (List.¬Any⇒All¬ (toList t) (¬p ∘ toList⁻))

-- More general than All¬⇒¬Any.
C-Any⇒All-C : {ℓC : Level} (C : Set ℓC) →
              ∀ {l u h} {t : Tree V l u h} →
              (Any P t → C) → All (λ kv → P kv → C) t
C-Any⇒All-C {V = V} {P = P} C {t = t} ¬any = All.map f (All-Any t)
  where
  f : {kv : K& V} → Any (kv ≡_) t → P kv → C
  f kv∈t p rewrite lookup-result kv∈t =
    ¬any (lookup-rebuild kv∈t p)

All¬⇒¬Any : ∀ {l u h} {t : Tree V l u h} →
            All (¬_ ∘ P) t → ¬ Any P t
All¬⇒¬Any ¬ps =
  (List.All¬⇒¬Any (toList-All⁺ ¬ps)) ∘ toList⁺

-- More general than All¬⇒¬Any.
All-C⇒C-Any : {ℓC : Level} (C : Set ℓC) →
              ∀ {l u h} {t : Tree V l u h} →
              All (λ kv → P kv → C) t → Any P t → C
All-C⇒C-Any C all¬ any = Any×All any all¬ (lookup-result any)

¬All⇒Any¬ : Decidable P → ∀ {l u h} {t : Tree V l u h} →
            (¬ All P t) → Any (¬_ ∘ P) t
¬All⇒Any¬ P? {t = t} ¬ps =
  toList⁻ (List.¬All⇒Any¬ P? (toList t) (¬ps ∘ toList-All⁻))

-- There is no more general ¬All⇒Any¬ with (C : Set ℓC).

Any¬⇒¬All : ∀ {l u h} {t : Tree V l u h} →
            Any (¬_ ∘ P) t → ¬ All P t
Any¬⇒¬All ¬ps =
  (List.Any¬⇒¬All (toList⁺ ¬ps)) ∘ toList-All⁺

-- More general than All¬⇒¬Any.
Any-C⇒C-All : {ℓC : Level} (C : Set ℓC) → ∀ {l u h} {t : Tree V l u h} →
            Any (λ kv → P kv → C) t → All P t → C
Any-C⇒C-All C any¬ all = lookup-result any¬ (Any×All any¬ all)

-- TODO: This _⇔_ can be made tighter.
--       For example Data.List.Relation.Unary.All.¬Any↠All¬ : (¬ Any P xs) ↠ All (¬_ ∘ P) xs
--       Also see what happens with my Function properties, where there should be an Inverse with
--       the _≗_ setoid on the right.
¬Any⇔All¬ : ∀ {l u h} {t : Tree V l u h} →
            (¬ Any P t) ⇔ All (¬_ ∘ P) t
¬Any⇔All¬ = mk⇔ ¬Any⇒All¬ All¬⇒¬Any

-- More general than ¬Any⇔All¬
C-Any⇔All-C : {ℓC : Level} (C : Set ℓC) → ∀ {l u h} → (t : Tree V l u h) →
              (Any P t → C) ⇔ All (λ kv → P kv → C) t
C-Any⇔All-C C t = mk⇔ (C-Any⇒All-C C) (All-C⇒C-Any C)

Any¬⇔¬All : Decidable P → ∀ {l u h} {t : Tree V l u h} →
            Any (¬_ ∘ P) t ⇔ (¬ All P t)
Any¬⇔¬All P? = mk⇔ Any¬⇒¬All (¬All⇒Any¬ P?)

-- There is no more general Any¬⇔¬All with (C : Set ℓC).
