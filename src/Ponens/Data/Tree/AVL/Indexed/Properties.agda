{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (StrictTotalOrder)

module Ponens.Data.Tree.AVL.Indexed.Properties
  {a ℓ₁ ℓ₂} (sto : StrictTotalOrder a ℓ₁ ℓ₂) where

open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_; Σ-syntax)
open import Data.Sum using (inj₁; inj₂)
open import Function using (_∘_)
open import Level using (Level; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Unary using (Pred)

open import Data.Tree.AVL.Indexed sto as AVL using (Tree; leaf; node; Value; K&_; key; Key⁺; _<_<_)
open import Data.Tree.AVL.Indexed.Relation.Unary.Any sto using (here)
open import Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties sto using (lookup⁺; lookup-result)
open import Ponens.Data.Tree.AVL.Indexed.Properties.Any sto using (_∈k_)

module STO = StrictTotalOrder sto
open STO using (module Eq; _≈_) renaming (Carrier to Key)

module _ {v : Level} {V : Value v} where
  private
    Val  = Value.family V

  lookup-nothing : ∀ {l u h} → (t : Tree V l u h) (k : Key) (v : Val k) (seg : l < k < u) →
                   AVL.lookup t k seg ≡ nothing → ¬ (k ∈k t)
  lookup-nothing t k v seg eq k∈t with lookup⁺ {P = (k ≈_) ∘ key} t k seg k∈t
  ... | inj₁ neq = neq (Eq.sym (lookup-result k∈t))
  ... | inj₂ (p≈k , eq-just) rewrite eq with eq-just
  ...   | ()

  fold-map : ∀ {a} → {A : Set a} → (A → A → A) → A → (K& V → A) → ∀ {l u h} → (t : Tree V l u h) → A
  fold-map _*_ e f (leaf l<u) = e
  fold-map _*_ e f (node kv l r _) = (fold-map _*_ e f l * f kv) * fold-map _*_ e f r

  Empty : ∀ {l u h} → (t : Tree V l u h) → Set (a ⊔ ℓ₁ ⊔ ℓ₂ ⊔ v)
  Empty t = (k : Key) → ¬ (k ∈k t)
  Empty? : ∀ {l u h} → (t : Tree V l u h) → Dec (Empty t)
  Empty? {h = zero} (leaf _) = yes λ _ ()
  Empty? {h = suc h} (node kv _ _ _) = no λ is-empty → is-empty (key kv) (here Eq.refl)

  Satisfiable : ∀ {l u h} → (t : Tree V l u h) → Set (a ⊔ ℓ₁ ⊔ ℓ₂ ⊔ v)
  Satisfiable t = Σ[ k ∈ Key ] k ∈k t
  Satisfiable? : ∀ {l u h} → (t : Tree V l u h) → Dec (Satisfiable t)
  Satisfiable? {h = zero} (leaf _) = no λ{()}
  Satisfiable? {h = suc h} (node kv _ _ _) = yes (key kv , here Eq.refl)
