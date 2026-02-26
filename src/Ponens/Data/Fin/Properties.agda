{-# OPTIONS --cubical-compatible --safe #-}

module Ponens.Data.Fin.Properties where

open import Data.Fin using (Fin)
open import Data.Fin.Properties using (+↔⊎)
import Data.Nat as ℕ
import Data.Nat.Properties as ℕ
open import Data.Sum using (_⊎_)
open import Data.Sum.Function.Propositional using (_⊎-↔_)
open import Function using (_↔_)
open import Function.Properties.Inverse using (↔-refl; ↔-trans)

-- Note that + is infixl and ⊎ is infixr.
Fin-+↔⊎3 : ∀ {l m n} → Fin (l ℕ.+ m ℕ.+ n) ↔ (Fin l ⊎ Fin m ⊎ Fin n)
Fin-+↔⊎3 {l} {m} {n}
  rewrite ℕ.+-assoc l m n =
  ↔-trans +↔⊎
          (↔-refl ⊎-↔ +↔⊎)
