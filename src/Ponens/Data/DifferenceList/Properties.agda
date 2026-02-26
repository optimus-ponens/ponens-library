{-
properties of Data.DifferenceList
-}

{-# OPTIONS --cubical-compatible --safe #-}

module Ponens.Data.DifferenceList.Properties where

open import Data.DifferenceList using (DiffList; lift; []; [_]; _∷_; _++_; _∷ʳ_; toList; fromList; map; take; drop)
open import Data.List as List using (List)
import Data.List.Properties as List
open import Data.List.Relation.Binary.Pointwise using (Pointwise)
open import Data.Nat using (ℕ)
open import Level using (Level; _⊔_)
open import Relation.Binary.Core using (REL)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Negation using (¬_)

private
  variable
    a b : Level
    A : Set a
    B : Set b

-- ~ relates a DiffList to the equivalent List.
infix 1 _~_
_~_ : {a : Level} {A : Set a} →
      DiffList A → List A → Set a
_~_ {A = A} xs ys = (k : List A) → xs k ≡ ys List.++ k

~REL : {ℓ a b : Level} {A : Set a} {B : Set b} →
       (R : REL A B ℓ) → DiffList A → List B → Set (a ⊔ b ⊔ ℓ)
~REL {A = A} {B = B} R xs ys =
  {xk : List A} {yk : List B} → Pointwise R xk ys →
  Pointwise R (xs xk) (ys List.++ yk)

-- TODO: The extra hypothesis isn't satisfied for ~take or ~drop. Is it useful?
~lift : {xs : DiffList A} {ys : List A} (f : List A → List A) →
        ((ys1 ys2 : List A) → f (ys1 List.++ ys2) ≡ f ys1 List.++ ys2) →
        xs ~ ys → lift f xs ~ f ys
~lift {ys = ys} f f-assoc is k rewrite is k = f-assoc ys k

~[] : ([] {A = A}) ~ List.[]
~[] k = refl

~∷ : {xs : DiffList A} {ys : List A} (x : A) → xs ~ ys → (x ∷ xs) ~ (x List.∷ ys)
~∷ {xs = xs} x is = ~lift {xs = xs} (x List.∷_) (λ _ _ → refl) is

~[_] : (x : A) → [ x ] ~ List.[ x ]
~[_] x k = refl

~++ : {xs1 xs2 : DiffList A} {ys1 ys2 : List A} → xs1 ~ ys1 → xs2 ~ ys2 → xs1 ++ xs2 ~ ys1 List.++ ys2
~++ {xs1 = xs1} {xs2} {ys1 = ys1} {ys2} ~1 ~2 k
  rewrite ~2 k | ~1 (ys2 List.++ k) | List.++-assoc ys1 ys2 k
  = refl

-- ++ with a single element in the middle:
~++-∷ : {xs1 xs2 : DiffList A} {ys1 ys2 : List A} → (x : A) → xs1 ~ ys1 → xs2 ~ ys2 → xs1 ++ (x ∷ xs2) ~ ys1 List.++ (x List.∷ ys2)
~++-∷ x ~1 ~2 = ~++ ~1 (~∷ x ~2)

~∷ʳ : {xs : DiffList A} {ys : List A} (x : A) → xs ~ ys → xs ∷ʳ x ~ ys List.∷ʳ x
~∷ʳ {ys = ys} x is k
  rewrite List.++-assoc ys (x List.∷ List.[]) k
  = is (x List.∷ k)

~toList : {xs : DiffList A} {ys : List A} → xs ~ ys → toList xs ≡ ys
~toList {ys = ys} is rewrite is List.[] = List.++-identityʳ ys

~fromList : (ys : List A) → fromList ys ~ ys
~fromList ys k = refl

~map : {xs : DiffList A} {ys : List A} (f : A → B) → xs ~ ys → map f xs ~ List.map f ys
~map {ys = ys} f is k rewrite is List.[] | List.++-identityʳ ys = refl

-- TODO: In order for ~concat to be usable we need a way to create the ~REL,
--       so we need to give a connection between ~REL and ~.
--       Something like: (~REL _≡_) ≡ _~_
{-
~concat : {xss : DiffList (DiffList A)} → {yss : List (List A)} →
          ~REL _~_ xss yss → concat xss ~ List.concat yss
~concat is k = {!!}
-}

module CounterintuitiveExamples where
  -- The following behavior of `take` is counterintuitive.
  -- The expected property does not hold: xs ~ ys → take n xs ~ List.take n ys
  _ : (take 0 (10 ∷ [])) (11 List.∷ List.[]) ≡ List.[]
  _ = refl
  _ : List.take 0 (10 List.∷ List.[]) List.++ 11 List.∷ List.[] ≡ 11 List.∷ List.[]
  _ = refl
  ¬~take : ¬ ({A : Set} → {xs : DiffList A} → {ys : List A} → (n : ℕ) → xs ~ ys → take n xs ~ List.take n ys)
  ¬~take ~take with ~take 0 (~fromList (10 List.∷ List.[])) (11 List.∷ List.[])
  ... | ()
  -- Instead we can use take as the last DiffList operation:
  []take : {xs : DiffList A} {ys : List A} (n : ℕ) → xs ~ ys → take n xs List.[] ≡ List.take n ys
  []take {ys = ys} n is rewrite is List.[] | List.++-identityʳ ys = refl

  -- `drop` has similar counterintuitive behaviour as `take`:
  ¬~drop : ¬ ({A : Set} → {xs : DiffList A} → {ys : List A} → (n : ℕ) → xs ~ ys → drop n xs ~ List.drop n ys)
  ¬~drop ~drop with ~drop 1 (~fromList List.[]) (11 List.∷ List.[])
  ... | ()
  -- Instead we can use drop as the last DiffList operation:
  []drop : {xs : DiffList A} {ys : List A} (n : ℕ) → xs ~ ys → drop n xs List.[] ≡ List.drop n ys
  []drop {ys = ys} n is rewrite is List.[] | List.++-identityʳ ys = refl
