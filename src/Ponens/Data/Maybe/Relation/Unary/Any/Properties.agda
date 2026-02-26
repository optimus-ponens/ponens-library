{-
TODO: Is this module used?
-}

{-# OPTIONS --cubical-compatible --safe #-}

module Ponens.Data.Maybe.Relation.Unary.Any.Properties where

open import Data.Maybe using (Maybe; just; map; maybe)
open import Data.Maybe.Relation.Unary.Any using (Any; just; drop-just)
open import Function using (_∘_)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Unary using (Pred)

private
  variable
    a b p q : Level
    A : Set a
    B : Set b
    P : Pred A p
    Q : Pred B q

-- TODO: Usage of this lemma seems like bad style because it's too obvious.
just→Any : (m : Maybe A) (x : A) → m ≡ just x → P x → Any P m
just→Any _ _ _≡_.refl = just

Any-elim : {c : Level} {C : Maybe A → Set c} →
           ((x : A) → P x → (m : Maybe A) → m ≡ just x → C m) →
           {m : Maybe A} →
           Any P m → C m
Any-elim f (just {x = x} Px) = f x Px (just x) _≡_.refl

Any-map⁻ : {f : A → B} {m : Maybe A} →
           Any Q (map f m) → Any (Q ∘ f) m
Any-map⁻ {Q = Q} {f = f} {m = m} =
  maybe {B = λ mx → Any Q (map f mx) → Any (Q ∘ f) mx}
        (λ x Py → just (drop-just Py))
        (λ ())
        m

Any-map⁺ : {f : A → B} {m : Maybe A} →
           Any (Q ∘ f) m → Any Q (map f m)
Any-map⁺ {Q = Q} {f = f} {m = m} =
  maybe {B = λ mx → Any (Q ∘ f) mx → Any Q (map f mx)}
        (λ x Pfx → just (drop-just Pfx))
        (λ ())
        m
