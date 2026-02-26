{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (StrictTotalOrder)

module Ponens.Data.Tree.AVL.Indexed.Properties.Cast
  {a ℓ₁ ℓ₂} (sto : StrictTotalOrder a ℓ₁ ℓ₂) where

open import Level using (Level) -- ; _⊔_)
open import Relation.Unary using (Pred)

open import Data.Tree.AVL.Indexed sto using (Tree; node; Value; K&_; _<⁺_; castˡ; castʳ)
open import Data.Tree.AVL.Indexed.Relation.Unary.Any sto using (Any; here; left; right)

private
  variable
    v p : Level
    V : Value v
    P : Pred (K& V) p

castˡ⁺ : ∀ {l m u h} {l<m : l <⁺ m} {mu : Tree V m u h} → Any P mu → Any P (castˡ l<m mu)
castˡ⁺ {mu = node _ _ _ _} (Any.here Pk) = here Pk
castˡ⁺ {mu = node _ _ _ _} (Any.left p) = left (castˡ⁺ p)
castˡ⁺ {mu = node _ _ _ _} (Any.right p) = right p

castˡ⁻ : ∀ {l m u h} {l<m : l <⁺ m} {mu : Tree V m u h} → Any P (castˡ l<m mu) → Any P mu
castˡ⁻ {mu = node _ _ _ _} (here Pk) = here Pk
castˡ⁻ {mu = node _ _ _ _} (left p) = left (castˡ⁻ p)
castˡ⁻ {mu = node _ _ _ _} (right p) = right p

castʳ⁺ : ∀ {l m u h} {lm : Tree V l m h} {m<u : m <⁺ u} → Any P lm → Any P (castʳ lm m<u)
castʳ⁺ {lm = node _ _ _ _} (here Pk) = here Pk
castʳ⁺ {lm = node _ _ _ _} (left p) = left p
castʳ⁺ {lm = node _ _ _ _} (right p) = right (castʳ⁺ p)

castʳ⁻ : ∀ {l m u h} {lm : Tree V l m h} {m<u : m <⁺ u} → Any P (castʳ lm m<u) → Any P lm
castʳ⁻ {lm = node _ _ _ _} (here Pk) = here Pk
castʳ⁻ {lm = node _ _ _ _} (left p) = left p
castʳ⁻ {lm = node _ _ _ _} (right p) = right (castʳ⁻ p)
