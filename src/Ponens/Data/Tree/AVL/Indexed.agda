{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (StrictTotalOrder)

module Ponens.Data.Tree.AVL.Indexed
  {a ℓ₁ ℓ₂} (sto : StrictTotalOrder a ℓ₁ ℓ₂) where

open import Data.Maybe using (Maybe; nothing; just)
open import Data.Product using (_,_; proj₁)
open import Level using (Level)
open import Relation.Binary using (tri<; tri≈; tri>)

open import Data.Tree.AVL.Indexed sto using (Tree; leaf; node; Value; K&_; _,_; _<_<_; [_]; headTail)

module STO = StrictTotalOrder sto
open STO using (_<_; compare) renaming (Carrier to Key)
open import Relation.Binary.Construct.Add.Extrema.Strict _<_ using ([_])

private
  variable
    v : Level
    V : Value v

head : ∀ {l u h} → Tree V l u h → Maybe (K& V)
head (leaf l<u) = nothing
head t@(node _ _ _ _) = just (proj₁ (headTail t))

-- Return the least element greater than the given key.
lookup-> : ∀ {l u h} → Tree V l u h → (k : Key) → l < k < u → Maybe (K& V)
lookup-> (leaf l<u) k l<k<u = nothing
lookup-> (node (k′ , v) lk′ k′u bal) k (l<k , k<u) with compare k′ k
lookup-> (node (k′ , v) lk′ k′u bal) k (l<k , k<u) | tri< k′<k _ _ =
  lookup-> k′u k ([ k′<k ] , k<u)
lookup-> (node (k′ , v) lk′ k′u bal) k (l<k , k<u) | tri≈ _ _ _ =
  head {l = [ k′ ]} k′u
lookup-> (node (k′ , v) lk′ k′u bal) k (l<k , k<u) | tri> _ _ k<k′
  with lookup-> lk′ k (l<k , [ k<k′ ])
... | just kv = just kv
... | nothing = just (k′ , v)
