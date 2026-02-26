{-
Properties having to do with List's Linked, Sorted, Unique.
-}
{-# OPTIONS --cubical-compatible --safe #-}

module Ponens.Data.List.Relation.Unary.Linked.Properties {a} {A : Set a} where

open import Data.Maybe using (just)
open import Data.Maybe.Relation.Binary.Connected using (Connected)
open import Data.List as List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Function using (flip)
open import Level using (Level)
open import Relation.Binary using (Rel)

open import Data.List.Relation.Unary.Linked {A = A} using (Linked; _∷_)

module _ {ℓ : Level} {R : Rel A ℓ} where
  All→Connected-last : (x : A) → {xs : List A} → All (flip R x) xs →
                       Connected R (List.last xs) (just x)
  All→Connected-last x [] = Connected.nothing-just
  All→Connected-last x (px ∷ []) = Connected.just px
  All→Connected-last x (_ ∷ pxs@(_ ∷ _)) = All→Connected-last x pxs

  All→Linked : (x : A) → {xs : List A} → All (R x) xs →
               Linked R xs → Linked R (x ∷ xs)
  All→Linked x {[]} xRxs pxs = Linked.[-]
  All→Linked x {y ∷ xs} (px ∷ xRxs) pxs = px ∷ pxs
