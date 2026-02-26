{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (StrictTotalOrder)

module Ponens.Data.Tree.AVL.Indexed.Properties.ToList
  {a ℓ₁ ℓ₂} (sto : StrictTotalOrder a ℓ₁ ℓ₂) where

import Data.DifferenceList as DiffList
open import Data.List using (List; _∷_; []; _++_)
import Data.List.Relation.Unary.All as ListAll
import Data.List.Relation.Unary.All.Properties as ListAll
import Data.List.Relation.Unary.Any as List
open import Data.List.Relation.Unary.Any.Properties using (++⁺ʳ; ++⁺ˡ; ++⁻)
open import Data.List.Relation.Unary.Linked using ([])
import Data.List.Relation.Unary.Linked.Properties as Linked
open import Data.Nat using (zero; suc)
open import Data.Product using (proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Function using (_on_)
open import Level using (Level; _⊔_)
open import Relation.Binary using (Rel)
import Relation.Binary.Construct.On as On
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Binary.Structures using (IsStrictTotalOrder)
open import Relation.Unary using (Pred)
import Ponens.Data.DifferenceList.Properties as DiffList
open import Ponens.Data.List.Relation.Unary.Linked.Properties using (All→Connected-last; All→Linked)

open import Data.Tree.AVL.Indexed sto using (Tree; leaf; node; Value; K&_; key; Key⁺; [_]; _∼_⊔_; toDiffList; toList)
open import Data.Tree.AVL.Indexed.Relation.Unary.All sto as All using (All; node; leaf)
open import Data.Tree.AVL.Indexed.Relation.Unary.Any sto using (Any; here; left; right)
open import Ponens.Data.Tree.AVL.Indexed.Properties.Range sto using (All-bounded)

module STO = StrictTotalOrder sto
open STO using (_≈_; _<_) renaming (Carrier to Key)
open import Relation.Binary.Construct.Add.Extrema.Strict _<_ using ([<]-injective)

module _ {v : Level} {V : Value v} where
  infix 4 _≈K&_ _<K&_
  _≈K&_ : Rel (K& V) ℓ₁
  _≈K&_ = _≈_ on key
  _<K&_ : Rel (K& V) ℓ₂
  _<K&_ = _<_ on key
  isStrictTotalOrderK& : IsStrictTotalOrder {a = a ⊔ v} {ℓ = ℓ₁} _≈K&_ {ℓ₂ = ℓ₂} _<K&_
  isStrictTotalOrderK& = On.isStrictTotalOrder key STO.isStrictTotalOrder
  strictTotalOrderK& : StrictTotalOrder (a ⊔ v) ℓ₁ ℓ₂
  strictTotalOrderK& = record { isStrictTotalOrder = isStrictTotalOrderK& }
  open import Ponens.Data.List.Relation.Unary.StrictSorted strictTotalOrderK& using () renaming (StrictSorted to StrictSortedK&) public

module _ {v : Level} {V : Value v} where
  toDiffList~ : ∀ {l u h} → (t : Tree V l u h) → toDiffList t DiffList.~ toList t
  toDiffList~ (leaf l<u) = DiffList.~[]
  toDiffList~ (node kv l r bal) rewrite toDiffList~ l (kv ∷ toDiffList r [])
    = DiffList.~++-∷ kv (toDiffList~ l) (toDiffList~ r)
  toList-node : ∀ {l u hˡ hʳ h} →
       (kv : K& V) → (lk : Tree V l [ key kv ] hˡ) → (ku : Tree V [ key kv ] u hʳ) → (bal : hˡ ∼ hʳ ⊔ h) →
       toList (node kv lk ku bal) ≡ toList lk ++ kv ∷ toList ku
  toList-node kv lk ku bal = toDiffList~ lk ((kv DiffList.∷ toDiffList ku) [])

  toList⁺ : {p : Level} {P : Pred (K& V) p} →
            ∀ {l u h} → {t : Tree V l u h} → Any P t → List.Any P (toList t)
  toList⁺ {t = node k l r bal} (here path) rewrite toList-node k l r bal
    = ++⁺ʳ (toDiffList l []) (List.here path)
  toList⁺ {t = node k l r bal} (left path) rewrite toList-node k l r bal
    = ++⁺ˡ (toList⁺ path)
  toList⁺ {t = node k l r bal} (right path) rewrite toList-node k l r bal
    = ++⁺ʳ (toDiffList l []) (List.there (toList⁺ path))

  toList⁻ : {p : Level} {P : Pred (K& V) p} →
            ∀ {l u h} → {t : Tree V l u h} → List.Any P (toList t) → Any P t
  toList⁻ {t = node k l r bal} path rewrite toList-node k l r bal with ++⁻ (toList l) path
  ... | inj₁ path-l = left (toList⁻ path-l)
  ... | inj₂ (List.here path-k) = here path-k
  ... | inj₂ (List.there path-r) = right (toList⁻ path-r)

  toList-All⁺ : {p : Level} {P : Pred (K& V) p} →
                ∀ {l u h} → {t : Tree V l u h} → All P t → ListAll.All P (toList t)
  toList-All⁺ {h = zero} {leaf l<u} p = ListAll.[]
  toList-All⁺ {h = suc h} {node kv lk ku bal} (node pkv plk pku)
    rewrite toList-node kv lk ku bal
    = ListAll.++⁺ (toList-All⁺ plk) (pkv ListAll.∷ toList-All⁺ pku)

  toList-All⁻ : {p : Level} {P : Pred (K& V) p} →
                ∀ {l u h} → {t : Tree V l u h} → ListAll.All P (toList t) → All P t
  toList-All⁻ {h = 0#} {leaf l<u} p = leaf
  toList-All⁻ {P = P} {h = suc h} {node kv lk ku bal} p
    rewrite toList-node kv lk ku bal
    = node (ListAll.head p-right)
                   (toList-All⁻ (ListAll.++⁻ˡ (toList lk) p))
                   (toList-All⁻ (ListAll.tail p-right))
    where
    p-right : ListAll.All P (kv ∷ toList ku)
    p-right = ListAll.++⁻ʳ (toList lk) p

  toList-StrictSorted : ∀ {l u h} → (t : Tree V l u h) → StrictSortedK& (toList t)
  toList-StrictSorted {h = zero} (leaf l<u) = []
  toList-StrictSorted {h = suc h} t@(node kv lk ku bal)
    rewrite toList-node kv lk ku bal =
    Linked.++⁺ (toList-StrictSorted lk)
               (All→Connected-last kv (toList-All⁺ lk-All))
               (All→Linked kv (toList-All⁺ ku-All) (toList-StrictSorted ku))
    where
    lk-All : All (_<K& kv) lk
    lk-All = All.map (λ p → [<]-injective (proj₂ p)) (All-bounded lk)
    ku-All : All (kv <K&_) ku
    ku-All = All.map (λ p → [<]-injective (proj₁ p)) (All-bounded ku)
