{-
The Agda stdlib doesn't have properties of delete.
Adding here them here.

Set membership properties of delete and insert:
∀ b → b ∈ delete a t ⇔ a ≉ b × b ∈ t
∀ b → b ∈ insert a t ⇔ a ≈ b ⊎ b ∈ t

Insert has a set Any property that's a generalization of ∈:
∀ P → Any P (insert a t) ⇔ P a ⊎ Any P t
Delete's Any property is weaker than the analogous generalization:
∀ P → Any P (delete a t) → Any P t

More properties:
* Relate Data.Tree.AVL.Indexed.lookup to Data.Tree.AVL.Indexed.Relation.Unary.Any.lookup.
This is Data.Tree.AVL.Indexed.Relation.Unary.Any.{lookup⁺ , lookup⁻}

*** Getting evaluation unstuck when writing proofs. ***
It's common when writing proofs for the evaluation to get stuck for mysterious reasons.
Let's say you want to write `foo-prop`, a property about the function `foo`.
`foo` splits into cases and has `with` clauses.

First copy the structure of `foo` as the body of `foo-prop`.
The RHS of each case of `foo-prop` should now be a ?.
When proving a particular case, if evaluation seems stuck then see if `foo arg₁ ... argₙ` evaluates to the case's RHS.
Use C-c C-n in the case's hole to try this evaluation.
If not, do something to get evaluation unstuck.

One gotcha is that `foo` might have light grey cases.
These happen when some pattern matching in the LHS is implicit.
This can cause evaluation to get stuck.
In `foo-prop` make sure that there's no light grey.
For example `join-left⁺` needed a `t₂₃@(node _ _ _ _)` instead of `t₂₃` to get evaluation unstuck.
This expanded pattern match is implied by {hʳ = suc hʳ} but wasn't being done in `join-left⁺`'s context.

Another gotcha is that you expect a term in the `?` in `with scrutinee\n... | pattern = ?` to evaluate `scrutinee` to `pattern`.
When this doesn't happen try:
* Simultaneous abstraction
https://agda.readthedocs.io/en/latest/language/with-abstraction.html#simultaneous-abstraction
Chain the term you expect to reduce in the with like `with scrutinee | term-that-should-reduce`.
* With-abstraction equality
https://agda.readthedocs.io/en/latest/language/with-abstraction.html#with-abstraction-equality
Write `with scrutinee in eq`. Now a the `eq` can do the reduction step via a `subst` or `rewrite`.
* simultaneous-equality-refl pattern:
`headTail-tail⁻` is an example of this pattern.
It uses simultaneous abstraction and with-abstraction equality and matches the eq with refl.
This pattern looks like:
foo args with pattern1 ← scrutinee1 in eq | more-scrutinees | eq
... | patterns | refl = ?
Often the scrutinee that's `in eq` is irrefutable, which looks like `with pattern1 ← scrutinee1` and means there's only one match.
-}

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (StrictTotalOrder)

module Ponens.Data.Tree.AVL.Indexed.Properties.Delete
  {a ℓ₁ ℓ₂} (sto : StrictTotalOrder a ℓ₁ ℓ₂) where

open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Level using (Level)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary using (Pred; _≐_; _∩_)

open import Data.Tree.AVL.Indexed sto using (Tree; leaf; node; Value; K&_; _,_; Key⁺; _<_<_; [_]ᴿ; delete)
open import Data.Tree.AVL.Indexed.Relation.Unary.Any sto using (Any; here; left; right; lookupKey)
open import Ponens.Data.Tree.AVL.Indexed.Properties.Any sto using (_∈k_; ∈k-bounded; lookupKey≉)
open import Ponens.Data.Tree.AVL.Indexed.Properties.Join sto using (join-node⁻; join⁻; join-left⁺; join-right⁺)
open import Ponens.Data.Tree.AVL.Indexed.Properties.JoinPieces sto using (joinʳ⁻-here⁺; joinʳ⁻-left⁺; joinʳ⁻-right⁺; joinˡ⁻⁻; joinʳ⁻⁻; joinˡ⁻-here⁺; joinˡ⁻-left⁺; joinˡ⁻-right⁺)

module STO = StrictTotalOrder sto
open STO using (module Eq; _<_) renaming (Carrier to Key)
open Eq using (_≉_)
open import Relation.Binary.Construct.Add.Extrema.Strict _<_ using ([<]-injective)

private
  variable
    v p : Level
    V : Value v
    P : Pred (K& V) p
    l u : Key⁺
    n : ℕ

delete-tree⁻ : (k : Key) (t : Tree V l u n) (seg : l < k < u) →
              (Any P (proj₂ (delete k t seg))) →
              Any P t
delete-tree⁻ k (node p@(k′ , v) lp pu bal) (l<k , k<u) path with STO.compare k′ k
delete-tree⁻ k (node p@(k′ , v) lp pu bal) (l<k , k<u) path | tri< k′<k _ _
  with joinʳ⁻⁻ p lp (delete k pu ([ k′<k ]ᴿ , k<u)) bal path
... | inj₁ path = here path
... | inj₂ (inj₁ path) = left path
... | inj₂ (inj₂ path) = right (delete-tree⁻ k pu ([ k′<k ]ᴿ , k<u) path)
delete-tree⁻ k (node p@(k′ , v) lp pu bal) (l<k , k<u) path | tri> _ _ k′>k
  with joinˡ⁻⁻ p (delete k lp (l<k , [ k′>k ]ᴿ)) pu bal path
... | inj₁ path = here path
... | inj₂ (inj₁ path) = left (delete-tree⁻ k lp (l<k , [ k′>k ]ᴿ) path)
... | inj₂ (inj₂ path) = right path
delete-tree⁻ k (node p@(k′ , v) lp pu bal) (l<k , k<u) path | tri≈ _ _ _ =
  join-node⁻ v lp pu bal path

delete-key⁻ : (k : Key) (t : Tree V l u n) (seg : l < k < u) →
             {kp : Key} → kp ∈k proj₂ (delete k t seg) →
             kp ≉ k
delete-key⁻ k (node p@(k′ , v) lp pu bal) (l<k , k<u) {kp} path kp≈k with STO.compare k′ k
delete-key⁻ k (node p@(k′ , v) lp pu bal) (l<k , k<u) {kp} path kp≈k | tri< k′<k k′≉k k′≯k
  with joinʳ⁻⁻ p lp (delete k pu ([ k′<k ]ᴿ , k<u)) bal path
... | inj₁ kp≈k′ = contradiction (Eq.trans (Eq.sym kp≈k′) kp≈k) k′≉k
... | inj₂ (inj₁ path') = contradiction (STO.<-respˡ-≈ kp≈k ([<]-injective (proj₂ (∈k-bounded path')))) k′≯k
... | inj₂ (inj₂ path') = delete-key⁻ k pu ([ k′<k ]ᴿ , k<u) path' kp≈k
delete-key⁻ k (node p@(k′ , v) lp pu bal) (l<k , k<u) {kp} path kp≈k | tri> k′≮k k′≉k k′>k
  with joinˡ⁻⁻ p (delete k lp (l<k , [ k′>k ]ᴿ)) pu bal path
... | inj₁ kp≈k′ = contradiction (Eq.trans (Eq.sym kp≈k′) kp≈k) k′≉k
... | inj₂ (inj₁ path') = delete-key⁻ k lp (l<k , [ k′>k ]ᴿ) path' kp≈k
... | inj₂ (inj₂ path') = contradiction (STO.<-respʳ-≈ kp≈k ([<]-injective (proj₁ (∈k-bounded path')))) k′≮k
delete-key⁻ k (node p@(k′ , v) lp pu bal) (l<k , k<u) {kp} path kp≈k | tri≈ k′≮k _ k′≯k
  with join⁻ lp pu bal path
... | inj₁ path' = contradiction (STO.<-respˡ-≈ kp≈k ([<]-injective (proj₂ (∈k-bounded path')))) k′≯k
... | inj₂ path' = contradiction (STO.<-respʳ-≈ kp≈k ([<]-injective (proj₁ (∈k-bounded path')))) k′≮k

delete⁺ : (k : Key) (t : Tree V l u n) (seg : l < k < u) →
          (path : Any P t) → lookupKey path ≉ k →
          Any P (proj₂ (delete k t seg))
delete⁺ k (leaf l<u) l<k<u path path≉k = path
delete⁺ k (node p@(k′ , v) lp pu bal) (l<k , k<u) path path≉k with STO.compare k′ k
delete⁺ k (node p@(k′ , v) lp pu bal) (l<k , k<u) path path≉k | tri< k′<k _ _ with path
... | here path' = joinʳ⁻-here⁺ p lp (delete k pu ([ k′<k ]ᴿ , k<u)) bal path'
... | left path' = joinʳ⁻-left⁺ p lp (delete k pu ([ k′<k ]ᴿ , k<u)) bal path'
... | right path' = joinʳ⁻-right⁺ p lp (delete k pu ([ k′<k ]ᴿ , k<u)) bal
                      (delete⁺ k pu ([ k′<k ]ᴿ , k<u) path' path≉k)
delete⁺ k (node p@(k′ , v) lp pu bal) (l<k , k<u) path path≉k | tri> _ _ k′>k with path
... | here path' = joinˡ⁻-here⁺ p (delete k lp (l<k , [ k′>k ]ᴿ)) pu bal path'
... | left path' = joinˡ⁻-left⁺ p (delete k lp (l<k , [ k′>k ]ᴿ)) pu bal
                     ((delete⁺ k lp (l<k , [ k′>k ]ᴿ)) path' path≉k)
... | right path' = joinˡ⁻-right⁺ p (delete k lp (l<k , [ k′>k ]ᴿ)) pu bal path'
delete⁺ k (node p@(k′ , v) lp pu bal) (l<k , k<u) path path≉k | tri≈ _ k′≈k _ with path
... | here path' = contradiction k′≈k path≉k
... | left path' = join-left⁺ lp pu bal path'
... | right path' = join-right⁺ lp pu bal path'

-- core property of delete:
delete∈ : (k : Key) (t : Tree V l u n) (seg : l < k < u) →
          (_∈k proj₂ (delete k t seg)) ≐ ((_≉ k) ∩ (_∈k t))
delete∈ k t seg = to , from
  where
  to : {x : Key} → (x∈ : x ∈k proj₂ (delete k t seg)) → (x ≉ k) × (x ∈k t)
  to x∈ = delete-key⁻ k t seg x∈
        , delete-tree⁻ k t seg x∈
  from : {x : Key} → x ≉ k × x ∈k t → x ∈k (proj₂ (delete k t seg))
  from (kp≉k , kp∈) = delete⁺ k t seg kp∈ (lookupKey≉ kp∈ kp≉k)
