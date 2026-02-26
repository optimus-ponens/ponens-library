{-# OPTIONS --cubical-compatible --safe #-}

module Ponens.Relation.Nullary.Properties where

open import Data.Bool using (false; true)
open import Level using (Level)
open import Relation.Nullary using (¬_; Dec; _because_; invert)

private
  variable
    a b : Level
    A : Set a
    B : Set b

Dec-elim : (A → B) → (¬ A → B) → Dec A → B
Dec-elim f g (true because [a]) = f (invert [a])
Dec-elim f g (false because [¬a]) = g (invert [¬a])
