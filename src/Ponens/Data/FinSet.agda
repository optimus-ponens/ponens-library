{-# OPTIONS --with-K --safe #-}

open import Relation.Binary.Bundles using (StrictTotalOrder)

module Ponens.Data.FinSet
  {a ℓ₁ ℓ₂} (sto : StrictTotalOrder a ℓ₁ ℓ₂) where

open import Ponens.Data.FinSet.Base sto public
