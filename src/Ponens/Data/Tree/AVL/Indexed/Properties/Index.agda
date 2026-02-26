{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (StrictTotalOrder)

module Ponens.Data.Tree.AVL.Indexed.Properties.Index
  {a ℓ₁ ℓ₂} (sto : StrictTotalOrder a ℓ₁ ℓ₂) where

open import Data.Fin as Fin using (Fin)
import Data.Fin.Properties as Fin
open import Data.List using (_∷_)
open import Data.List.Properties using (length-++)
open import Data.Nat using (zero; suc; _+_)
open import Data.Nat.Properties using (+-suc; +-assoc)
open import Data.Product using (Σ-syntax)
open import Data.Sum using (_⊎_)
open import Data.Sum.Function.Propositional using (_⊎-↔_)
open import Function using (_∘_; _↔_; Inverse)
open import Function.Properties.Inverse using (↔-refl; ↔-sym; ↔-trans)
open import Function.Related.TypeIsomorphisms using (⊎-comm; ⊎-assoc)
open import Level using (Level)
open import Ponens.Data.Fin.Properties using (Fin-+↔⊎3)
open import Ponens.Function using (mk↔-∘)
open import Ponens.Function.Related.TypeIsomorphisms using (Σ≡↔⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Unary using (Pred)

open import Data.Tree.AVL.Indexed sto using (Tree; leaf; node; Value; K&_; key; Key⁺; [_]; _<⁺_; _∼_⊔_; size; toList)
open import Ponens.Data.Tree.AVL.Indexed.Properties.ToList sto using (toList-node)
open import Ponens.Data.Tree.AVL.Indexed.Properties.Any sto using (_∈_; ∈↔⊎)

module STO = StrictTotalOrder sto
open STO using () renaming (Carrier to Key)

module _ {v : Level} {V : Value v} {l u : Key⁺} where
  -- This one orders indices on the tree's preorder.
  size-node-preorder : ∀ {hˡ hʳ h} (kv : K& V) (lk : Tree V l [ key kv ] hˡ)
              (ku : Tree V [ kv .key ] u hʳ) (bal : hˡ ∼ hʳ ⊔ h) →
              size (node kv lk ku bal) ≡ 1 + size lk + size ku
  size-node-preorder kv lk ku bal
    rewrite toList-node kv lk ku bal
          | length-++ (toList lk) {ys = kv ∷ toList ku}
          | +-suc (size lk) (size ku)
    = refl

  -- This one orders indices in the tree's order.
  size-node-keyorder : ∀ {hˡ hʳ h} (kv : K& V) (lk : Tree V l [ kv .key ] hˡ)
              (ku : Tree V [ kv .key ] u hʳ) (bal : hˡ ∼ hʳ ⊔ h) →
              size (node kv lk ku bal) ≡ size lk + 1 + size ku
  size-node-keyorder kv lk ku bal
    rewrite toList-node kv lk ku bal
          | length-++ (toList lk) {ys = kv ∷ toList ku}
          | +-assoc (size lk) 1 (size ku)
    = refl

module _ {v : Level} {V : Value v} where
  index↔∈-leaf : ∀ {l u} (l<u : l <⁺ u) → Fin 0 ↔ (Σ[ kv ∈ K& V ] (kv ∈ leaf l<u))
  index↔∈-leaf l<u = mk↔-∘ (λ ()) (λ ()) (λ ()) (λ ())

  mutual
    index↔∈ : ∀ {l u h} (t : Tree V l u h) → Fin (size t) ↔ (Σ[ kv ∈ K& V ] (kv ∈ t))
    index↔∈ {h = zero} (leaf l<u) = index↔∈-leaf l<u
    index↔∈ {h = suc h} (node kv lk ku bal) = index↔∈-node kv lk ku bal

    index↔∈-node : ∀ {l u hˡ hʳ h} (kv : K& V) (lk : Tree V l [ kv .key ] hˡ) →
            (ku : Tree V [ kv .key ] u hʳ) (bal : hˡ ∼ hʳ ⊔ h) →
            Fin (size (node kv lk ku bal)) ↔ (Σ[ kv' ∈ K& V ] (kv' ∈ node kv lk ku bal))
    -- levels on sides are different so reasoning syntax is difficult
    index↔∈-node kv lk ku bal =
       ↔-trans size-node-Fin
      (↔-trans Fin-+↔⊎3
      (↔-trans swap-⊎
      (↔-trans (kv↔ ⊎-↔ index↔∈ lk ⊎-↔ index↔∈ ku)
               (↔-sym ∈↔⊎))))
      where
      -- Give the index a type that results in indices corresponding to the keyorder.
      size-node-Fin : Fin (size (node kv lk ku bal)) ↔ Fin (size lk + 1 + size ku)
      size-node-Fin rewrite size-node-keyorder kv lk ku bal = ↔-refl
      swap-⊎ : (Fin (size lk) ⊎ Fin 1 ⊎ Fin (size ku)) ↔ (Fin 1 ⊎ Fin (size lk) ⊎ Fin (size ku))
      -- TODO: Try using an algebra solver.
      -- TODO: Or instead lift ↔ along ⊎-assoc.
      swap-⊎ =
         ↔-trans (↔-sym (⊎-assoc _ _ _ _))
        (↔-trans (⊎-comm _ _ ⊎-↔ ↔-refl)
                 (⊎-assoc _ _ _ _))
      kv↔ : Fin 1 ↔ (Σ[ kv' ∈ K& V ] (kv' ≡ kv))
      kv↔ = ↔-trans Fin.1↔⊤ (↔-sym (Σ≡↔⊤ kv))

  index→∈ : ∀ {l u h} (t : Tree V l u h) → Fin (size t) → (Σ[ kv ∈ K& V ] (kv ∈ t))
  index→∈ = Inverse.to ∘ index↔∈
  ∈→index : ∀ {l u h} (t : Tree V l u h) → (Σ[ kv ∈ K& V ] (kv ∈ t)) → Fin (size t)
  ∈→index = Inverse.from ∘ index↔∈
