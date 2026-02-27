{-
The type here `St` is an ordered set.
It is interpreted as a Unary Pred on keys, using ⟦_⟧.
Each op is shown to have equivalent semantics in terms of Pred op.

Universe levels:
All the (Pred Key ℓ)s should have the same ℓ.
This means:
* We can use equational reasoning.
* We can use the stdlib's Unary properties instead of the universe-hetergenous properties I added to stdlib-Unary.
* We can use the Relation.Unary.Algebra.

TODO:
* More functions from other libraries:
  The union of Relation.Unary and Haskell's Data.Set are pretty comprehensive.
  * powerSet (Haskell)
  * Unary._⟨×⟩_ (Haskell's cartesianProduct)
  * Unary._⟨⊎⟩_ (Haskell's disjointUnion)
  * Unary._⟨⊙⟩_
  * Unary._~
  * Unary._⟨∘⟩_ -- wait until finite binary rel is implemented
  * Unary._//_ -- This is implementable because only Cs in Q need to be considered -- consider waiting until finite binary rel is implemented
  * Unary._\\_ -- same as Unary._//_
  * Union monoid. Is there a commutative monoid?
  * Intersection semigroup.
  * Disjoint property (same type as ∩)
  * Delete property with hypothesis that elem is in the set.
* Rename St to OrdSet, if that name isn't already taken in stdlib. (The total Map could be named FinFun).
  `St` sometimes names state.
  Also rename FinSet to OrdSet. This is like the Lean stdlib.
* See if we can use a solver, possibly with Relation.Unary.Algebra.
* toString and fromString. First define a Repr for generic data, which will be the intermediary.
* Should there be a {to,from}SetList, which would be a list representation of a set?
  There would be an Equivalence between the two representations.
  Currently we have toList-StrictSorted, which proves that toList produces a StrictSorted List.
  See Data.List.Relation.Binary.BagAndSetEquality for a possibly suitable List representation of Sets.
* lookup-≥ lookup-< lookup-≤
  lookup-> was already added so these should be relatively easy.
  First decide whether lookup-> should be cleaned up.
  Consider adding a swap wrapper to reuse symmetrical functions (same for headTail and initLast).
* Improve the efficiency of fromList from O(n * log n) to O(n).
* Improve the efficiency of ⟦size⟧'s index↔Key from O(n) to O(log n).
  This requires changing the AVL representation so each node contains its size.
-}

{-# OPTIONS --with-K --safe #-}

open import Relation.Binary.Bundles using (StrictTotalOrder)

module Ponens.Data.FinSet.Base
  {a ℓ₁ ℓ₂} (sto-hetero-ℓ : StrictTotalOrder a ℓ₁ ℓ₂) where

open import Data.Fin using (Fin)
open import Data.List as List using (List; []; _∷_)
open import Data.List.Properties using (length-map; partition-defn)
import Data.List.Relation.Binary.Lex as ListLex
import Data.List.Relation.Binary.Lex.Strict as ListLexStrict
open import Data.List.Relation.Binary.Pointwise using (Pointwise)
import Data.List.Relation.Unary.Any.Properties as ListAny
import Data.List.Relation.Unary.Linked.Properties as Linked
open import Data.Maybe as Maybe using (Maybe; nothing; just)
open import Data.Maybe.Relation.Unary.Any using () renaming (Any to MaybeAny)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product as × using (_×_; _,_; proj₁; proj₂; Σ; Σ-syntax; ∃; ∃-syntax)
open import Data.Sum as ⊎ using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
import Data.Unit.Polymorphic as Poly
open import Function using (id; _∘_; _on_; _⇔_; _↔_; mk⇔; Inverse)
import Function.Construct.Composition as Composition
import Function.Properties.Equivalence as Equivalence
open import Function.Properties.Inverse using (↔-refl; ↔-trans)
open import Level using (Level; _⊔_; 0ℓ)
import Ponens.Data.Maybe.Relation.Unary.Any.Properties as MaybeAny
import Ponens.Relation.Binary.Construct.Subst.Equality as Equality
open import Ponens.Relation.Unary.Properties as U using (↔→≐; ≐-∁; ∁-∪≐∩-∁; P∪[Q∩R]≐P∪R; Decidable→∁; P∩[Q∪R]≐P∩R; Empty-∁∩; ℓ-∩-comm; ℓ-∩-congʳ; ≐→Empty⇔)
open import Relation.Binary as Binary using (Rel)
open import Relation.Binary.Bundles using (Setoid; StrictPartialOrder)
open import Relation.Binary.Consequences using (resp⇒¬-resp)
import Relation.Binary.Construct.On as On
open import Relation.Binary.Definitions using (_Respects_; _Respects₂_; _Respectsˡ_; _Respectsʳ_; Reflexive; Symmetric; Transitive; Trans; Irreflexive)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
open import Relation.Binary.Structures using (IsStrictTotalOrder; IsStrictPartialOrder; IsEquivalence)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable as Nullary using (¬?; _×-dec_)
open import Relation.Nullary.Construct.Add.Extrema using (⊥±; ⊤±; [_])
open import Relation.Unary as U using (Pred)
import Relation.Unary.Algebra as U
import Relation.Unary.Polymorphic as U-poly
import Relation.Unary.Properties as U
import Relation.Unary.Relation.Binary.Equality as Equality

{-
Aligned level.
This enables:
* ≐'s equational reasoning
* use of stdlib's Unary/Properties, which are universe homogenous
* use of Algebra library
-}
open import Ponens.Relation.Binary.Align using (alignStrictTotalOrder)
ℓa : Level
ℓa = a ⊔ ℓ₁ ⊔ ℓ₂
sto : StrictTotalOrder a ℓa ℓa
sto = alignStrictTotalOrder sto-hetero-ℓ

open import Data.Tree.AVL.Indexed sto as Indexed using (Tree; leaf; node; Value; const; K&_; key; Key⁺; _<⁺_; ⊥⁺; ⊤⁺; _⊕_; pred[_⊕_]; ⊥⁺<[_]<⊤⁺; ⊥⁺<[_]; [_]<⊤⁺)
import Data.Tree.AVL.Indexed.Relation.Unary.All sto as All
import Data.Tree.AVL.Indexed.Relation.Unary.Any sto as Any
open import Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties sto using (lookup⁻; singleton⁻; singleton⁺; insert⁻; Any-insert-nothing; Any-insert-just; insert⁺; lookup-result; lookup-rebuild)
import Ponens.Data.Tree.AVL.Indexed sto as PonensIndexed
open import Ponens.Data.Tree.AVL.Indexed.Properties sto as IndexedProperties using (lookup-nothing)
open import Ponens.Data.Tree.AVL.Indexed.Properties.Any sto using (lookupKey≉) renaming (_∈_ to _∈≡_)
open import Ponens.Data.Tree.AVL.Indexed.Properties.AnyWithK sto using (KV-Inverse-Key)
open import Ponens.Data.Tree.AVL.Indexed.Properties.Cast sto using (castˡ⁻; castˡ⁺; castʳ⁻; castʳ⁺)
import Ponens.Data.Tree.AVL.Indexed.Properties.Delete sto as Delete
open import Ponens.Data.Tree.AVL.Indexed.Properties.Gap sto using (Gap; Gap-cong₂)
open import Ponens.Data.Tree.AVL.Indexed.Properties.HeadTail sto using (headTail-head⁻; headTail-tail⁻; headTail⁺; initLast-last⁻; initLast-init⁻; initLast⁺)
open import Ponens.Data.Tree.AVL.Indexed.Properties.Index sto using (index↔∈)
open import Ponens.Data.Tree.AVL.Indexed.Properties.Lookup sto using (lookup->⁻; lookup->⁺)
open import Ponens.Data.Tree.AVL.Indexed.Properties.Range sto using (∈-ex-ex; ∈-ex-ex?; ∈-ex-ex-resp; ∈-inc-ex?; ∈-inc-ex; ∈-inc-ex-resp; ∈-inc-ex-⊥)
open import Ponens.Data.List.Relation.Unary.StrictSorted sto using (StrictSorted; StrictSorted-≐→Pointwise)
open import Ponens.Data.Tree.AVL.Indexed.Properties.ToList sto as ToList using (toList⁻; toList⁺)

module STO = StrictTotalOrder sto
open STO using (module Eq; _≈_; _<_; _≟_) renaming (Carrier to Key)
open Eq using (_≉_; setoid)
import Data.List.Membership.Setoid setoid as ListMem
open import Ponens.Data.List.Membership.Setoid.Properties setoid using (filter⇔∩; Pointwise→∈)
open import Relation.Binary.Construct.Add.Extrema.Strict _<_ using (⊥±<⊤±)
import Relation.Binary.Reasoning.Setoid (Equality.≐-setoid Key ℓa) as ≐-Reasoning

U∅ : Pred Key ℓa
U∅ = U-poly.∅ {ℓ = ℓa}
UU : Pred Key ℓa
UU = U-poly.U {ℓ = ℓa}

V : Value 0ℓ
V = const ⊤
private
  Val  = Value.family V
  Val≈ = Value.respects V

record St : Set ℓa where
  constructor mkSt
  field
    height : ℕ
    tree : Tree V ⊥± ⊤± height
open St using (height; tree)

Σ→St : {h : ℕ} → (∃ λ i → Tree V ⊥± ⊤± (i ⊕ h)) → St
Σ→St {h} (i , t) = mkSt (i ⊕ h) t
Σpred→St : {h : ℕ} → (∃ λ i → Tree V ⊥± ⊤± pred[ i ⊕ h ]) → St
Σpred→St {h} (i , t) = mkSt pred[ i ⊕ h ] t

-- Any
Any : ∀ {ℓ} → (P : Pred Key ℓ) → (t : St) → Set (ℓa ⊔ ℓ)
Any P t = Any.Any (P ∘ key) (tree t)
any? : ∀ {ℓ} → {P : Pred Key ℓ} → (P? : U.Decidable P) → (t : St) → Dec (Any P t)
any? P? t = Any.any? (P? ∘ key) (tree t)

-- All
All : ∀ {ℓ} → (P : Pred Key ℓ) → (t : St) → Set (ℓa ⊔ ℓ)
All P t = All.All (P ∘ key) (tree t)
all? : ∀ {ℓ} → {P : Pred Key ℓ} → (P? : U.Decidable P) → (t : St) → Dec (All P t)
all? P? t = All.all? (P? ∘ key) (tree t)

-- member
infix 4 _∈_ _∉_ _∈?_
_∈_ : Key → St → Set ℓa
_∈_ k = Any (k ≈_)
_∉_ : Key → St → Set ℓa
_∉_ k t = ¬ (k ∈ t)
-- Note: Use of any? would be simpler but would be O(n) time instead of O(log n) time.
_∈?_ : (k : Key) → (t : St) → Dec (k ∈ t)
_∈?_ k t with Indexed.lookup (tree t) k ⊥⁺<[ k ]<⊤⁺
            | lookup⁻ (tree t) k tt (⊥⁺<[ k ]<⊤⁺)
            | lookup-nothing (tree t) k tt (⊥⁺<[ k ]<⊤⁺)
... | just tt | p⁻ | _ = yes (Any.map (λ{ (k′≈k , _) → Eq.sym k′≈k }) (p⁻ ≡.refl))
... | nothing | _ | p⁺ = no (p⁺ ≡.refl)

-- Meaning of an St
⟦_⟧ : St → Pred Key ℓa
⟦_⟧ t k = k ∈ t
⟦_⟧? : ∀ t → U.Decidable ⟦ t ⟧
⟦_⟧? t = _∈? t

-- Alternate meaining of an St
⟦_⟧-Keys : St → Set ℓa
⟦_⟧-Keys t = Σ Key ⟦ t ⟧
⟦_⟧-Keys-setoid : St → Setoid ℓa ℓa
⟦_⟧-Keys-setoid t = On.setoid setoid (proj₁ {B = ⟦ t ⟧})

-- Properties of ∈
P∈ : Key → K& V → Set ℓa
P∈ k = (k ≈_) ∘ key
P∈? : (k : Key) → (kv : K& V) → Dec (P∈ k kv)
P∈? k = (k ≟_) ∘ key
P∈-resp-≈ : {k1 k2 : Key} → {kv : K& V} → k1 ≈ k2 → P∈ k1 kv → P∈ k2 kv
P∈-resp-≈ k1≈k2 k1≈kv = Eq.trans (Eq.sym k1≈k2) k1≈kv
∈-resp-≈ : ∀ {t} → (_∈ t) Respects _≈_
∈-resp-≈ eq = Any.map (P∈-resp-≈ eq)
∈≡↔⟦-⟧-Keys : (t : St) → Inverse (≡.setoid (Σ (K& V) (_∈≡ (tree t))))
                                 (⟦ t ⟧-Keys-setoid)
∈≡↔⟦-⟧-Keys t = KV-Inverse-Key (tree t)

-- Properties of List and Unary's Preds.
∅≐∈ : U∅ U.≐ (ListMem._∈ [])
∅≐∈ = (λ ()) , λ ()
U≐∉ : UU U.≐ (ListMem._∉ [])
U≐∉ = (λ _ ()) , λ _ → Poly.tt
U≐∈∷ : (k : Key) → (ks : List Key) → ((_≈ k) U.∪ (ListMem._∈ ks)) U.≐ (ListMem._∈ (k ∷ ks))
U≐∈∷ k ks = ↔→≐ (λ k' → ListAny.∷↔ (k' ≈_))
∩≐∉∷ : (k : Key) → (ks : List Key) → ((_≉ k) U.∩ (ListMem._∉ ks)) U.≐ (ListMem._∉ (k ∷ ks))
∩≐∉∷ k ks = begin
  (_≉ k) U.∩ (ListMem._∉ ks)
    ≈⟨ U.≐-sym (∁-∪≐∩-∁ {A = Key} (_≈ k) (ListMem._∈ ks)) ⟩
  U.∁ ((_≈ k) U.∪ (ListMem._∈ ks))
    ≈⟨ ≐-∁ (U≐∈∷ k ks) ⟩
  ListMem._∉ (k ∷ ks) ∎
  where open ≐-Reasoning
filter∈≐∩ : (u : St) → (ks : List Key) → (ListMem._∈ (List.filter (_∈? u) ks)) U.≐ ((ListMem._∈ ks) U.∩ ⟦ u ⟧)
filter∈≐∩ u ks = filter⇔∩ (_∈? u) ∈-resp-≈ ks

-- Semantics of the Maybe container
⟦_⟧-Maybe : Maybe Key → Pred Key ℓa
⟦_⟧-Maybe m k = MaybeAny (k ≈_) m

-- meaning of ∈
⟦∈⟧ : (t : St) → (U._∈ ⟦ t ⟧) U.≐ (_∈ t)
⟦∈⟧ t = U.≐-refl

∅ : St
∅ = mkSt 0 (Indexed.empty ⊥±<⊤±)
⟦∅⟧ : ⟦ ∅ ⟧ U.≐ U∅
⟦∅⟧ = (λ ()) , λ ()

singleton : Key → St
singleton k = mkSt 1 (Indexed.singleton k tt ⊥⁺<[ k ]<⊤⁺)
⟦singleton⟧ : (k : Key) → ⟦ singleton k ⟧ U.≐ (_≈ k)
⟦singleton⟧ k = singleton⁻ k tt (⊥⁺<[ k ]<⊤⁺)
              , singleton⁺ k tt (⊥⁺<[ k ]<⊤⁺)

insert : Key → St → St
insert k (mkSt h t) = Σ→St (Indexed.insert k tt t (⊥⁺<[ k ]<⊤⁺))
⟦insert⟧⁻ : ∀ k t → ⟦ insert k t ⟧ U.⊆ (_≈ k) U.∪ ⟦ t ⟧
⟦insert⟧⁻ k t {k'} k'∈t' =
  ⊎.map id (Any.map proj₂)
    (insert⁻ {P = P∈ k'}
             (λ k3≈k2 k1≈k2 → Eq.trans k1≈k2 (Eq.sym k3≈k2))
             k tt (tree t) ⊥⁺<[ k ]<⊤⁺ k'∈t')
⟦insert⟧-key⁺ : ∀ k t → k ∈ insert k t
⟦insert⟧-key⁺ k t with k ∈? t
... | no k∉t = Any-insert-nothing k tt (tree t) ⊥⁺<[ k ]<⊤⁺ Eq.refl k∉t
... | yes k∈t = Any-insert-just k tt (tree t) ⊥⁺<[ k ]<⊤⁺ (λ _ → id) k∈t
⟦insert⟧-tree⁺ : ∀ {k t k'} → k' ∈ t → k' ∈ insert k t
⟦insert⟧-tree⁺ {k = k} {t} {k'} k∈t with k ≟ k'
... | no k≉k' = insert⁺ k tt (tree t) ⊥⁺<[ k ]<⊤⁺ k∈t
                  (lookupKey≉ k∈t (k≉k' ∘ Eq.sym) ∘ Eq.sym)
... | yes k≈k' = ∈-resp-≈ k≈k' (⟦insert⟧-key⁺ k t)
⟦insert⟧ : (k : Key) (t : St) → ⟦ insert k t ⟧ U.≐ (_≈ k) U.∪ ⟦ t ⟧
⟦insert⟧ k t =
    (⟦insert⟧⁻ _ _)
  , λ{ (inj₁ k'≈k) → ∈-resp-≈ (Eq.sym k'≈k) (⟦insert⟧-key⁺ k t)
     ; (inj₂ k'∈t) → ⟦insert⟧-tree⁺ k'∈t}

delete : Key → St → St
delete k (mkSt h t) = Σpred→St {h = h} (Indexed.delete k t ⊥⁺<[ k ]<⊤⁺)
⟦delete⟧ : (k : Key) (t : St) → ⟦ delete k t ⟧ U.≐ (_≉ k) U.∩ ⟦ t ⟧
⟦delete⟧ k t = Delete.delete∈ k (tree t) ⊥⁺<[ k ]<⊤⁺

insert-idem : ∀ k t → ⟦ insert k (insert k t) ⟧ U.≐ ⟦ insert k t ⟧
insert-idem k t = begin
  ⟦ insert k (insert k t) ⟧
    ≈⟨ (⟦insert⟧ k (insert k t)) ⟩
  (_≈ k) U.∪ ⟦ insert k t ⟧
    ≈⟨ (U.∪-congʳ (⟦insert⟧ k t)) ⟩
  (_≈ k) U.∪ ((_≈ k) U.∪ ⟦ t ⟧)
    ≈⟨ (U.∪-idemˡ (_≈ k) ⟦ t ⟧) ⟩
  (_≈ k) U.∪ ⟦ t ⟧
    ≈⟨ (U.≐-sym (⟦insert⟧ k t)) ⟩
  ⟦ insert k t ⟧ ∎
  where open ≐-Reasoning
delete-idem : ∀ k t → ⟦ delete k (delete k t) ⟧ U.≐ ⟦ delete k t ⟧
delete-idem k t = begin
  ⟦ delete k (delete k t) ⟧
    ≈⟨ (⟦delete⟧ k (delete k t)) ⟩
  (_≉ k) U.∩ ⟦ delete k t ⟧
    ≈⟨ (U.∩-congʳ (⟦delete⟧ k t)) ⟩
  (_≉ k) U.∩ ((_≉ k) U.∩ ⟦ t ⟧)
    ≈⟨ (U.∩-idemˡ (_≉ k) ⟦ t ⟧) ⟩
  (_≉ k) U.∩ ⟦ t ⟧
    ≈⟨ (U.≐-sym (⟦delete⟧ k t)) ⟩
  ⟦ delete k t ⟧ ∎
  where open ≐-Reasoning
insert-delete-idem : ∀ k t → ⟦ insert k (delete k t) ⟧ U.≐ ⟦ insert k t ⟧
insert-delete-idem k t = begin
  ⟦ insert k (delete k t) ⟧
    ≈⟨ (⟦insert⟧ k (delete k t)) ⟩
  (_≈ k) U.∪ ⟦ delete k t ⟧
    ≈⟨ (U.∪-congʳ (⟦delete⟧ k t)) ⟩
  (_≈ k) U.∪ ((_≉ k) U.∩ ⟦ t ⟧)
    ≈⟨ (P∪[Q∩R]≐P∪R (Decidable→∁ (_≟ k)) ⟦ t ⟧) ⟩
  (_≈ k) U.∪ ⟦ t ⟧
    ≈⟨ (U.≐-sym (⟦insert⟧ k t)) ⟩
  ⟦ insert k t ⟧ ∎
  where open ≐-Reasoning
delete-insert-idem : ∀ k t → ⟦ delete k (insert k t) ⟧ U.≐ ⟦ delete k t ⟧
delete-insert-idem k t = begin
  ⟦ delete k (insert k t) ⟧
    ≈⟨ (⟦delete⟧ k (insert k t)) ⟩
  (_≉ k) U.∩ ⟦ insert k t ⟧
    ≈⟨ (U.∩-congʳ (⟦insert⟧ k t)) ⟩
  (_≉ k) U.∩ ((_≈ k) U.∪ ⟦ t ⟧)
    ≈⟨ (P∩[Q∪R]≐P∩R {P = _≉ k} {Q = _≈ k} (Empty-∁∩ (_≈ k)) ⟦ t ⟧) ⟩
  (_≉ k) U.∩ ⟦ t ⟧
    ≈⟨ (U.≐-sym (⟦delete⟧ k t)) ⟩
  ⟦ delete k t ⟧ ∎
  where open ≐-Reasoning

toList : St → List Key
toList (mkSt h t) = List.map key (Indexed.toList t)
⟦toList⟧ : (t : St) → (ListMem._∈ (toList t)) U.≐ ⟦ t ⟧
⟦toList⟧ t = toList⁻ ∘ ListAny.map⁻
           , ListAny.map⁺ ∘ toList⁺
toList-StrictSorted : (t : St) → StrictSorted (toList t)
toList-StrictSorted t = Linked.map⁺ (ToList.toList-StrictSorted (tree t))

inserts : List Key → St → St
inserts ks t = List.foldr insert t ks
⟦inserts⟧ : (ks : List Key) → (t : St) → ⟦ inserts ks t ⟧ U.≐ (ListMem._∈ ks) U.∪ ⟦ t ⟧
⟦inserts⟧ [] t = begin
  ⟦ inserts [] t ⟧
    ≈⟨ U.≐-refl ⟩
  ⟦ t ⟧
    ≈⟨ (U.≐-sym (U.∪-identityˡ ⟦ t ⟧)) ⟩
  U∅ U.∪ ⟦ t ⟧
    ≈⟨ (U.∪-congˡ ∅≐∈) ⟩
  (ListMem._∈ []) U.∪ ⟦ t ⟧ ∎
  where open ≐-Reasoning
⟦inserts⟧ (k ∷ ks) t = begin
  ⟦ inserts (k ∷ ks) t ⟧
    ≈⟨ U.≐-refl ⟩
  ⟦ insert k (inserts ks t) ⟧
    ≈⟨ (⟦insert⟧ k (inserts ks t)) ⟩
  (_≈ k) U.∪ ⟦ inserts ks t ⟧
    ≈⟨ (U.∪-congʳ (⟦inserts⟧ ks t)) ⟩
  (_≈ k) U.∪ ((ListMem._∈ ks) U.∪ ⟦ t ⟧)
    ≈⟨ (U.≐-sym (U.∪-assoc (_≈ k) (ListMem._∈ ks) ⟦ t ⟧)) ⟩
  ((_≈ k) U.∪ (ListMem._∈ ks)) U.∪ ⟦ t ⟧
    ≈⟨ (U.∪-congˡ (U≐∈∷ k ks)) ⟩
  (ListMem._∈ (k ∷ ks)) U.∪ ⟦ t ⟧ ∎
  where open ≐-Reasoning

deletes : List Key → St → St
deletes ks t = List.foldr delete t ks
⟦deletes⟧ : (ks : List Key) → (t : St) → ⟦ deletes ks t ⟧ U.≐ (ListMem._∉ ks) U.∩ ⟦ t ⟧
⟦deletes⟧ [] t = begin
  ⟦ deletes [] t ⟧
    ≈⟨ U.≐-refl ⟩
  ⟦ t ⟧
    ≈⟨ (U.≐-sym (U.∩-identityˡ ⟦ t ⟧)) ⟩
  UU U.∩ ⟦ t ⟧
    ≈⟨ U.∩-congˡ U≐∉ ⟩
  (ListMem._∉ []) U.∩ ⟦ t ⟧ ∎
  where open ≐-Reasoning
⟦deletes⟧ (k ∷ ks) t = begin
  ⟦ deletes (k ∷ ks) t ⟧
    ≈⟨ U.≐-refl ⟩
  ⟦ delete k (deletes ks t) ⟧
    ≈⟨ (⟦delete⟧ k (deletes ks t)) ⟩
  (_≉ k) U.∩ ⟦ (deletes ks t) ⟧
    ≈⟨ (U.∩-congʳ (⟦deletes⟧ ks t)) ⟩
  (_≉ k) U.∩ (ListMem._∉ ks) U.∩ ⟦ t ⟧
    ≈⟨ (U.≐-sym (U.∩-assoc (_≉ k) (ListMem._∉ ks) ⟦ t ⟧)) ⟩
  ((_≉ k) U.∩ (ListMem._∉ ks)) U.∩ ⟦ t ⟧
    ≈⟨ (U.∩-congˡ (∩≐∉∷ k ks)) ⟩
  (ListMem._∉ (k ∷ ks)) U.∩ ⟦ t ⟧ ∎
  where open ≐-Reasoning

fromList : List Key → St
fromList ks = inserts ks ∅
⟦fromList⟧ : (ks : List Key) → ⟦ fromList ks ⟧ U.≐ (ListMem._∈ ks)
⟦fromList⟧ ks = begin
  ⟦ fromList ks ⟧
    ≈⟨ U.≐-refl ⟩
  ⟦ inserts ks ∅ ⟧
    ≈⟨ (⟦inserts⟧ ks ∅) ⟩
  (ListMem._∈ ks) U.∪ ⟦ ∅ ⟧
    ≈⟨ (U.∪-congʳ ⟦∅⟧) ⟩
  (ListMem._∈ ks) U.∪ U∅
    ≈⟨ (U.∪-identityʳ (ListMem._∈ ks)) ⟩
  (ListMem._∈ ks) ∎
  where open ≐-Reasoning
≐-fromList : {ks1 ks2 : List Key} → (ListMem._∈ ks1) U.≐ (ListMem._∈ ks2) →
             ⟦ fromList ks1 ⟧ U.≐ ⟦ fromList ks2 ⟧
≐-fromList {ks1} {ks2} eq = begin
    ⟦ fromList ks1 ⟧
      ≈⟨ ⟦fromList⟧ ks1 ⟩
    ListMem._∈ ks1
      ≈⟨ eq ⟩
    ListMem._∈ ks2
      ≈⟨ U.≐-sym (⟦fromList⟧ ks2) ⟩
    ⟦ fromList ks2 ⟧ ∎
  where open ≐-Reasoning

foldr : ∀ {a} → {A : Set a} → (Key → A → A) → A → St → A
foldr f x t = List.foldr f x (toList t)
foldr-List : ∀ {a} → {A : Set a} (f : Key → A → A) (x : A) (t : St) →
             List.foldr f x (toList t) ≡ foldr f x t
foldr-List f x t = ≡.refl

size : St → ℕ
size = foldr (λ _ → suc) 0
size-List : ∀ t → size t ≡ List.length (toList t)
size-List t = ≡.refl
size-Indexed : ∀ t → size t ≡ Indexed.size (tree t)
size-Indexed t = length-map key (Indexed.toList (tree t))

-- A helper for ⟦size⟧ that covers the ↔ part of the Inverse.
size↔ : (t : St) → Fin (size t) ↔ (Σ (K& V) (_∈≡ (tree t)))
size↔ t =
  ↔-trans size-Indexed-Fin
          (index↔∈ (tree t))
  where
  size-Indexed-Fin : Fin (size t) ↔ Fin (Indexed.size (tree t))
  size-Indexed-Fin rewrite size-Indexed t = ↔-refl
-- ⟦size⟧ identifies Keys with numeric indices.
⟦size⟧ : (t : St) → Inverse (≡.setoid (Fin (size t))) (⟦ t ⟧-Keys-setoid)
⟦size⟧ t =
  Composition.inverse (size↔ t)
                      (∈≡↔⟦-⟧-Keys t)
key→index : ∀ {k t} → k ∈ t → Fin (size t)
key→index {k} {t = t} k∈t = Inverse.from (⟦size⟧ t) (k , k∈t)
index→key : ∀ {t} → Fin (size t) → Σ[ k ∈ Key ] k ∈ t
index→key {t} = Inverse.to (⟦size⟧ t)

filter : ∀ {ℓ} {P : Pred Key ℓ} → U.Decidable P → St → St
filter P? = fromList ∘ List.filter P? ∘ toList
⟦filter⟧ : ∀ {ℓ} {P : Pred Key ℓ} (P? : U.Decidable P) → (P Respects _≈_) →
           (t : St) → ⟦ filter P? t ⟧ U.≐ P U.∩ ⟦ t ⟧
-- Universe levels of two sides are different so can't use reasoning syntax.
⟦filter⟧ {P = P} P? resp t =
   U.≐-trans (⟦fromList⟧ ((List.filter P? (toList t))))
  (U.≐-trans (filter⇔∩ P? resp (toList t))
  (U.≐-trans (ℓ-∩-comm (ListMem._∈ toList t) P)
             (ℓ-∩-congʳ (⟦toList⟧ t))))

partition : ∀ {ℓ} {P : Pred Key ℓ} → U.Decidable P → St → St × St
partition P? = ×.map fromList fromList ∘ List.partition P? ∘ toList
⟦partition⟧-yes : ∀ {ℓ} {P : Pred Key ℓ} (P? : U.Decidable P) → (P Respects _≈_) →
               (t : St) → ⟦ proj₁ (partition P? t) ⟧ U.≐ P U.∩ ⟦ t ⟧
-- Universe levels of two sides are different so can't use reasoning syntax.
⟦partition⟧-yes P? resp t =
   U.≐-trans (≐-fromList List-parition≐filter)
             (⟦filter⟧ P? resp t)
  where
  List-parition≐filter : (ListMem._∈ (proj₁ (List.partition P? (toList t))))
                         U.≐ (ListMem._∈ (List.filter P? (toList t)))
  List-parition≐filter rewrite partition-defn P? (toList t) = U.≐-refl
⟦partition⟧-no : ∀ {ℓ} {P : Pred Key ℓ} (P? : U.Decidable P) → (P Respects _≈_) →
               (t : St) → ⟦ proj₂ (partition P? t) ⟧ U.≐ U.∁ P U.∩ ⟦ t ⟧
-- Universe levels of two sides are different so can't use reasoning syntax.
⟦partition⟧-no {P = P} P? resp t =
   U.≐-trans (≐-fromList List-parition≐filter)
             (⟦filter⟧ (U.∁? P?) (resp⇒¬-resp {_∼_ = _≈_} Eq.sym resp) t)
  where
  List-parition≐filter : (ListMem._∈ (proj₂ (List.partition P? (toList t))))
                         U.≐ (ListMem._∈ (List.filter (U.∁? P?) (toList t)))
  List-parition≐filter rewrite partition-defn P? (toList t) = U.≐-refl

headTail : St → Maybe (Key × St)
headTail (mkSt zero (leaf l<u)) = nothing
headTail (mkSt (suc h) t@(node kv lk ku bal)) =
  let k , _ , (i , tail) = Indexed.headTail t
  in just (key k , mkSt (i ⊕ h) (Indexed.castˡ ⊥⁺<[ key k ] tail))
⟦headTail⟧ : (t : St) →
             U.Maybe→Pred (λ{ (k , u) → (k ≈_) U.∪ ⟦ u ⟧}) (headTail t)
             U.≐ ⟦ t ⟧
⟦headTail⟧ (mkSt zero (leaf l<u)) = (λ ()) , λ ()
⟦headTail⟧ (mkSt (suc h) t@(node _ _ _ _)) =
    (λ{ (inj₁ head≈k) → headTail-head⁻ t (Eq.sym head≈k)
      ; (inj₂ k∈tail) → headTail-tail⁻ t (castˡ⁻ k∈tail)})
  , (⊎.map Eq.sym castˡ⁺ ∘ headTail⁺ t)

initLast : St → Maybe (Key × St)
initLast (mkSt zero (leaf l<u)) = nothing
initLast (mkSt (suc h) t@(node kv lk ku bal)) =
  let k , _ , (i , init) = Indexed.initLast t
  in just (key k , mkSt (i ⊕ h) (Indexed.castʳ init [ key k ]<⊤⁺))
⟦initLast⟧ : (t : St) →
             U.Maybe→Pred (λ{ (k , u) → (k ≈_) U.∪ ⟦ u ⟧}) (initLast t)
             U.≐ ⟦ t ⟧
⟦initLast⟧ (mkSt zero (leaf l<u)) = (λ ()) , λ ()
⟦initLast⟧ (mkSt (suc h) t@(node _ _ _ _)) =
    (λ{ (inj₁ last≈k) → initLast-last⁻ t (Eq.sym last≈k)
      ; (inj₂ k∈init) → initLast-init⁻ t (castʳ⁻ k∈init)})
  , (⊎.map Eq.sym castʳ⁺ ∘ initLast⁺ t)

lookup-> : St → Key → Maybe Key
lookup-> t k =
  Maybe.map key (PonensIndexed.lookup-> (tree t) k ⊥⁺<[ k ]<⊤⁺)
⟦lookup->⟧⁻ : ∀ t k → ∀ {k′} →
              ⟦ lookup-> t k ⟧-Maybe k′ →
              ⟦ t ⟧ k′ × (k < k′) × ¬ Any (Gap k k′) t
⟦lookup->⟧⁻ t k {k′} eq-just =
  let (k′∈t , k<kv , ¬gap) = lookup->⁻ (tree t) k (⊥⁺<[ k ]<⊤⁺) (MaybeAny.Any-map⁻ eq-just)
      k′≈lookup = lookup-result k′∈t
  in k′∈t ,
     STO.<-respʳ-≈ (Eq.sym k′≈lookup) k<kv ,
     ¬gap ∘ Any.map λ gap → Gap-cong₂ gap k′≈lookup
⟦lookup->⟧⁺ : ∀ t k → ∀ {k′} →
              ⟦ t ⟧ k′ × (k < k′) × ¬ Any (Gap k k′) t →
              ⟦ lookup-> t k ⟧-Maybe k′
⟦lookup->⟧⁺ t k {k′} (k′∈t , k<k′ , ¬gap) =
  MaybeAny.Any-map⁺ (lookup->⁺ (tree t) k (⊥⁺<[ k ]<⊤⁺)
                  k′∈t
                  (STO.<-respʳ-≈ k′≈lookup k<k′)
                  (¬gap ∘ Any.map λ gap → Gap-cong₂ gap (Eq.sym k′≈lookup)))
  where
  k′≈lookup : k′ ≈ (Any.lookupKey k′∈t)
  k′≈lookup = lookup-result k′∈t
⟦lookup->⟧ : ∀ t k →
             ⟦ lookup-> t k ⟧-Maybe
             U.≐ (⟦ t ⟧ U.∩ (k <_) U.∩ λ k2 → ¬ Any (Gap k k2) t)
⟦lookup->⟧ t k = ⟦lookup->⟧⁻ t k , ⟦lookup->⟧⁺ t k

{-
lookup-≥ : St → Key → Maybe Key
lookup-≥ t k with k ∈? t
... | yes _ = just k
... | no _ = lookup-> t k
⟦lookup-≥⟧ : ∀ t k →
             ⟦ lookup-≥ t k ⟧-Maybe
             U.≐ (⟦ t ⟧ U.∩ (k ≤_) U.∩ λ k2 → ¬ Any (λ k3 → k ≤ k3 × k3 < k2) t)
⟦lookup-≥⟧ t k = {!!}
-}

-- range-exclusive excludes lower, excludes upper
-- TODO: Implement this on Indexed so it can be O(output + log n) instead of O(n).
range-exclusive : Key⁺ → Key⁺ → St → St
range-exclusive lo hi = filter (∈-ex-ex? lo hi)
⟦range-exclusive⟧ : (lo hi : Key⁺) → (t : St) → ⟦ range-exclusive lo hi t ⟧ U.≐ ∈-ex-ex lo hi U.∩ ⟦ t ⟧
⟦range-exclusive⟧ lo hi t = ⟦filter⟧ (∈-ex-ex? lo hi) (∈-ex-ex-resp lo hi) t

-- range includes lower, excludes upper
-- TODO: Implement this on Indexed so it can be O(output + log n) instead of O(n).
range : Key⁺ → Key⁺ → St → St
range lo hi = filter (∈-inc-ex? lo hi)
⟦range⟧ : (lo hi : Key⁺) → (t : St) → ⟦ range lo hi t ⟧ U.≐ ∈-inc-ex lo hi U.∩ ⟦ t ⟧
⟦range⟧ lo hi t = ⟦filter⟧ (∈-inc-ex? lo hi) (∈-inc-ex-resp lo hi) t

-- If k is in t then the left side excludes k and the right side includes k.
split : Key⁺ → St → St × St
split k t = range ⊥⁺ k t , range k ⊤⁺ t
⟦split⟧₁ : ∀ k t → ⟦ proj₁ (split k t) ⟧ U.≐ (λ k′ → [ k′ ] <⁺ k) U.∩ ⟦ t ⟧
⟦split⟧₁ k t = begin
  ⟦ proj₁ (split k t) ⟧
    ≈⟨ U.≐-refl ⟩
  ⟦ range ⊥⁺ k t ⟧
    ≈⟨ ⟦range⟧ ⊥⁺ k t ⟩
  ∈-inc-ex ⊥⁺ k U.∩ ⟦ t ⟧
    ≈⟨ U.ℓ-∩-congˡ (∈-inc-ex-⊥ k) ⟩
  (λ k′ → [ k′ ] <⁺ k) U.∩ ⟦ t ⟧ ∎
  where open ≐-Reasoning

infixr 7 _∩_
infixr 6 _∪_
infixr 6 _∖_

_∪_ : St → St → St
t ∪ u = inserts (toList t) u
⟦∪⟧ : (t u : St) → ⟦ t ∪ u ⟧ U.≐ ⟦ t ⟧ U.∪ ⟦ u ⟧
⟦∪⟧ t u = begin
  ⟦ t ∪ u ⟧
    ≈⟨ (⟦inserts⟧ (toList t) u) ⟩
  (ListMem._∈ (toList t)) U.∪ ⟦ u ⟧
    ≈⟨ (U.∪-congˡ (⟦toList⟧ t)) ⟩
  ⟦ t ⟧ U.∪ ⟦ u ⟧ ∎
  where open ≐-Reasoning

_∩_ : St → St → St
_∩_ t u = fromList (List.filter (_∈? u) (toList t))
⟦∩⟧ : (t u : St) → ⟦ t ∩ u ⟧ U.≐ ⟦ t ⟧ U.∩ ⟦ u ⟧
⟦∩⟧ t u = begin
  ⟦ t ∩ u ⟧
    ≈⟨ (⟦fromList⟧ (List.filter (_∈? u) (toList t))) ⟩
  (ListMem._∈ (List.filter (_∈? u) (toList t)))
    ≈⟨ (filter∈≐∩ u (toList t)) ⟩
  (ListMem._∈ (toList t)) U.∩ ⟦ u ⟧
    ≈⟨ (U.∩-congˡ (⟦toList⟧ t)) ⟩
  ⟦ t ⟧ U.∩ ⟦ u ⟧ ∎
  where open ≐-Reasoning

_∖_ : St → St → St
_∖_ t u = deletes (toList u) t
⟦∖⟧ : (t u : St) → ⟦ t ∖ u ⟧ U.≐ ⟦ t ⟧ U.∖ ⟦ u ⟧
⟦∖⟧ t u = begin
  ⟦ t ∖ u ⟧
    ≈⟨ (⟦deletes⟧ (toList u) t) ⟩
  (ListMem._∉ (toList u)) U.∩ ⟦ t ⟧
    ≈⟨ ((U.∩-congˡ (≐-∁ (⟦toList⟧ u)))) ⟩
  U.∁ ⟦ u ⟧ U.∩ ⟦ t ⟧
    ≈⟨ (U.∩-comm (_∉ u) ⟦ t ⟧) ⟩
  ⟦ t ⟧ U.∩ U.∁ ⟦ u ⟧
    ≈⟨ U.≐-refl ⟩
  ⟦ t ⟧ U.∖ ⟦ u ⟧ ∎
  where open ≐-Reasoning

symmetricDifference : St → St → St
symmetricDifference t u = (t ∪ u) ∖ (t ∩ u)
⟦symmetricDifference⟧ : (t u : St) → ⟦ symmetricDifference t u ⟧ U.≐ ((⟦ t ⟧ U.∪ ⟦ u ⟧) U.∖ (⟦ t ⟧ U.∩ ⟦ u ⟧))
⟦symmetricDifference⟧ t u = begin
  ⟦ symmetricDifference t u ⟧
    ≈⟨ U.≐-refl ⟩
  ⟦ (t ∪ u) ∖ (t ∩ u) ⟧
    ≈⟨ ⟦∖⟧ (t ∪ u) (t ∩ u) ⟩
  ⟦ t ∪ u ⟧ U.∖ ⟦ t ∩ u ⟧
    ≈⟨ U.∖-cong (⟦∪⟧ t u) (⟦∩⟧ t u) ⟩
  (⟦ t ⟧ U.∪ ⟦ u ⟧) U.∖ (⟦ t ⟧ U.∩ ⟦ u ⟧)  ∎
  where open ≐-Reasoning

-- TODO: Try using Relation.Unary.Algebra for the following ∩ and ∪ properties.
∩-cong : {t1 t2 u1 u2 : St} → ⟦ t1 ⟧ U.≐ ⟦ t2 ⟧ → ⟦ u1 ⟧ U.≐ ⟦ u2 ⟧ → ⟦ t1 ∩ u1 ⟧ U.≐ ⟦ t2 ∩ u2 ⟧
∩-cong {t1} {t2} {u1} {u2} t12 u12 = begin
  ⟦ t1 ∩ u1 ⟧
    ≈⟨ (⟦∩⟧ t1 u1) ⟩
  ⟦ t1 ⟧ U.∩ ⟦ u1 ⟧
    ≈⟨ (U.∩-cong t12 u12) ⟩
  ⟦ t2 ⟧ U.∩ ⟦ u2 ⟧
    ≈⟨ (U.≐-sym (⟦∩⟧ t2 u2)) ⟩
  ⟦ t2 ∩ u2 ⟧ ∎
  where open ≐-Reasoning
∩-comm : (t u : St) → ⟦ t ∩ u ⟧ U.≐ ⟦ u ∩ t ⟧
∩-comm t u = begin
  ⟦ t ∩ u ⟧
    ≈⟨ (⟦∩⟧ t u) ⟩
  ⟦ t ⟧ U.∩ ⟦ u ⟧
    ≈⟨ (U.∩-comm ⟦ t ⟧ ⟦ u ⟧) ⟩
  ⟦ u ⟧ U.∩ ⟦ t ⟧
    ≈⟨ (U.≐-sym (⟦∩⟧ u t)) ⟩
  ⟦ u ∩ t ⟧ ∎
  where open ≐-Reasoning
∩-assoc : (t u v : St) → ⟦ (t ∩ u) ∩ v ⟧ U.≐ ⟦ t ∩ (u ∩ v) ⟧
∩-assoc t u v = begin
  ⟦ (t ∩ u) ∩ v ⟧
    ≈⟨ (⟦∩⟧ (t ∩ u) v) ⟩
  ⟦ t ∩ u ⟧ U.∩ ⟦ v ⟧
    ≈⟨ (U.∩-congˡ (⟦∩⟧ t u)) ⟩
  (⟦ t ⟧ U.∩ ⟦ u ⟧) U.∩ ⟦ v ⟧
    ≈⟨ (U.∩-assoc ⟦ t ⟧ ⟦ u ⟧ ⟦ v ⟧) ⟩
  ⟦ t ⟧ U.∩ (⟦ u ⟧ U.∩ ⟦ v ⟧)
    ≈⟨ (U.≐-sym (U.∩-congʳ (⟦∩⟧ u v))) ⟩
  ⟦ t ⟧ U.∩ (⟦ u ∩ v ⟧)
    ≈⟨ (U.≐-sym (⟦∩⟧ t (u ∩ v))) ⟩
  ⟦ t ∩ (u ∩ v) ⟧ ∎
  where open ≐-Reasoning
∩-idem : (t : St) → ⟦ t ∩ t ⟧ U.≐ ⟦ t ⟧
∩-idem t = begin
  ⟦ t ∩ t ⟧
    ≈⟨ (⟦∩⟧ t t) ⟩
  ⟦ t ⟧ U.∩ ⟦ t ⟧
    ≈⟨ (U.∩-idem ⟦ t ⟧) ⟩
  ⟦ t ⟧ ∎
  where open ≐-Reasoning
∩-zeroˡ : (t : St) → ⟦ ∅ ∩ t ⟧ U.≐ ⟦ ∅ ⟧
∩-zeroˡ t = begin
  ⟦ ∅ ∩ t ⟧
    ≈⟨ (⟦∩⟧ ∅ t) ⟩
  ⟦ ∅ ⟧ U.∩ ⟦ t ⟧
    ≈⟨ U.∩-congˡ ⟦∅⟧ ⟩
  U∅ U.∩ ⟦ t ⟧
    ≈⟨ (U.∩-zeroˡ ⟦ t ⟧) ⟩
  U∅
    ≈⟨ (U.≐-sym ⟦∅⟧) ⟩
  ⟦ ∅ ⟧ ∎
  where open ≐-Reasoning
∩-zeroʳ : (t : St) → ⟦ t ∩ ∅ ⟧ U.≐ ⟦ ∅ ⟧
∩-zeroʳ t = begin
  ⟦ t ∩ ∅ ⟧
    ≈⟨ (⟦∩⟧ t ∅) ⟩
  ⟦ t ⟧ U.∩ ⟦ ∅ ⟧
    ≈⟨ (U.∩-congʳ ⟦∅⟧) ⟩
  ⟦ t ⟧ U.∩ U∅
    ≈⟨ (U.∩-zeroʳ ⟦ t ⟧) ⟩
  U∅
    ≈⟨ (U.≐-sym ⟦∅⟧) ⟩
  ⟦ ∅ ⟧ ∎
  where open ≐-Reasoning

∪-cong : {t1 t2 u1 u2 : St} → ⟦ t1 ⟧ U.≐ ⟦ t2 ⟧ → ⟦ u1 ⟧ U.≐ ⟦ u2 ⟧ → ⟦ t1 ∪ u1 ⟧ U.≐ ⟦ t2 ∪ u2 ⟧
∪-cong {t1} {t2} {u1} {u2} t12 u12 = begin
  ⟦ t1 ∪ u1 ⟧
    ≈⟨ (⟦∪⟧ t1 u1) ⟩
  ⟦ t1 ⟧ U.∪ ⟦ u1 ⟧
    ≈⟨ (U.∪-cong t12 u12) ⟩
  ⟦ t2 ⟧ U.∪ ⟦ u2 ⟧
    ≈⟨ (U.≐-sym (⟦∪⟧ t2 u2)) ⟩
  ⟦ t2 ∪ u2 ⟧ ∎
  where open ≐-Reasoning
∪-comm : (t u : St) → ⟦ t ∪ u ⟧ U.≐ ⟦ u ∪ t ⟧
∪-comm t u = begin
  ⟦ t ∪ u ⟧
    ≈⟨ (⟦∪⟧ t u) ⟩
  ⟦ t ⟧ U.∪ ⟦ u ⟧
    ≈⟨ (U.∪-comm ⟦ t ⟧ ⟦ u ⟧) ⟩
  ⟦ u ⟧ U.∪ ⟦ t ⟧
    ≈⟨ (U.≐-sym (⟦∪⟧ u t)) ⟩
  ⟦ u ∪ t ⟧ ∎
  where open ≐-Reasoning
∪-assoc : (t u v : St) → ⟦ (t ∪ u) ∪ v ⟧ U.≐ ⟦ t ∪ (u ∪ v) ⟧
∪-assoc t u v = begin
  ⟦ (t ∪ u) ∪ v ⟧
    ≈⟨ (⟦∪⟧ (t ∪ u) v) ⟩
  ⟦ (t ∪ u) ⟧ U.∪ ⟦ v ⟧
    ≈⟨ (U.∪-congˡ (⟦∪⟧ t u)) ⟩
  (⟦ t ⟧ U.∪ ⟦ u ⟧) U.∪ ⟦ v ⟧
    ≈⟨ (U.∪-assoc ⟦ t ⟧ ⟦ u ⟧ ⟦ v ⟧) ⟩
  ⟦ t ⟧ U.∪ (⟦ u ⟧ U.∪ ⟦ v ⟧)
    ≈⟨ (U.≐-sym (U.∪-congʳ (⟦∪⟧ u v))) ⟩
  ⟦ t ⟧ U.∪ (⟦ u ∪ v ⟧)
    ≈⟨ (U.≐-sym (⟦∪⟧ t (u ∪ v))) ⟩
  ⟦ t ∪ (u ∪ v) ⟧ ∎
  where open ≐-Reasoning
∪-idem : (t : St) → ⟦ t ∪ t ⟧ U.≐ ⟦ t ⟧
∪-idem t = begin
  ⟦ t ∪ t ⟧
    ≈⟨ (⟦∪⟧ t t) ⟩
  ⟦ t ⟧ U.∪ ⟦ t ⟧
    ≈⟨ (U.∪-idem ⟦ t ⟧) ⟩
  ⟦ t ⟧ ∎
  where open ≐-Reasoning
∪-identityˡ : (t : St) → ⟦ ∅ ∪ t ⟧ U.≐ ⟦ t ⟧
∪-identityˡ t = begin
  ⟦ ∅ ∪ t ⟧
    ≈⟨ (⟦∪⟧ ∅ t) ⟩
  ⟦ ∅ ⟧ U.∪ ⟦ t ⟧
    ≈⟨ (U.∪-congˡ ⟦∅⟧) ⟩
  U∅ U.∪ ⟦ t ⟧
    ≈⟨ (U.∪-identityˡ ⟦ t ⟧) ⟩
  ⟦ t ⟧ ∎
  where open ≐-Reasoning
∪-identityʳ : (t : St) → ⟦ t ∪ ∅ ⟧ U.≐ ⟦ t ⟧
∪-identityʳ t = begin
  ⟦ t ∪ ∅ ⟧
    ≈⟨ (⟦∪⟧ t ∅) ⟩
  ⟦ t ⟧ U.∪ ⟦ ∅ ⟧
    ≈⟨ (U.∪-congʳ ⟦∅⟧) ⟩
  ⟦ t ⟧ U.∪ U∅
    ≈⟨ (U.∪-identityʳ ⟦ t ⟧) ⟩
  ⟦ t ⟧ ∎
  where open ≐-Reasoning

insert≐singleton-∪ : ∀ k t → ⟦ insert k t ⟧ U.≐ ⟦ singleton k ∪ t ⟧
insert≐singleton-∪ k t = U.≐-refl
delete≐∖-singleton : ∀ k t → ⟦ delete k t ⟧ U.≐ ⟦ t ∖ singleton k ⟧
delete≐∖-singleton k t = U.≐-refl

Empty : St → Set ℓa
Empty t = U.Empty ⟦ t ⟧
Empty? : U.Decidable Empty
Empty? t = IndexedProperties.Empty? (tree t)

Satisfiable : St → Set ℓa
Satisfiable t = U.Satisfiable ⟦ t ⟧
Satisfiable≡∈ : ∀ t → Satisfiable t ≡ (∃[ k ] k ∈ t)
Satisfiable≡∈ t = ≡.refl
Satisfiable? : U.Decidable Satisfiable
Satisfiable? t = IndexedProperties.Satisfiable? (tree t)

Universal : St → Set ℓa
Universal t = U.Universal ⟦ t ⟧
-- Universal is not Decidable.

infix 4 _⊆_ _⊆?_ _⊇_ _⊇?_ _⊈_ _⊈?_ _⊉_ _⊉?_ _⊂_ _⊂?_ _⊃_ _⊃?_ _⊄_ _⊄?_ _⊅_ _⊅?_ _≐_ _≐?_ _≬_ _≬?_

_⊆_ : Rel St ℓa
t ⊆ u = ⟦ t ⟧ U.⊆ ⟦ u ⟧
Empty-∖ : (t u : St) → Empty (t ∖ u) ⇔ ⟦ t ⟧ U.⊆ ⟦ u ⟧
Empty-∖ t u =
   Equivalence.trans (≐→Empty⇔ (⟦∖⟧ t u))
                     (U.Empty-∖⇔⊆ ⟦ t ⟧ ⟦ u ⟧?)
_⊆?_ : Binary.Decidable _⊆_
t ⊆? u = Nullary.map (Empty-∖ _ _) (Empty? (t ∖ u))

_⊇_ : Rel St ℓa
t ⊇ u = ⟦ t ⟧ U.⊇ ⟦ u ⟧
_⊇?_ : Binary.Decidable _⊇_
t ⊇? u = u ⊆? t

_⊈_ : Rel St ℓa
t ⊈ u = ⟦ t ⟧ U.⊈ ⟦ u ⟧
_⊈?_ : Binary.Decidable _⊈_
t ⊈? u = ¬? (t ⊆? u)

_⊉_ : Rel St ℓa
t ⊉ u = ⟦ t ⟧ U.⊉ ⟦ u ⟧
_⊉?_ : Binary.Decidable _⊉_
t ⊉? u = u ⊈? t

_⊂_ : Rel St ℓa
t ⊂ u = ⟦ t ⟧ U.⊂ ⟦ u ⟧
_⊂?_ : Binary.Decidable _⊂_
t ⊂? u = t ⊆? u ×-dec (u ⊈? t)

_⊃_ : Rel St ℓa
t ⊃ u = ⟦ t ⟧ U.⊃ ⟦ u ⟧
_⊃?_ : Binary.Decidable _⊃_
t ⊃? u = u ⊂? t

_⊄_ : Rel St ℓa
t ⊄ u = ⟦ t ⟧ U.⊄ ⟦ u ⟧
_⊄?_ : Binary.Decidable _⊄_
t ⊄? u = ¬? (t ⊂? u)

_⊅_ : Rel St ℓa
t ⊅ u = ⟦ t ⟧ U.⊅ ⟦ u ⟧
_⊅?_ : Binary.Decidable _⊅_
t ⊅? u = u ⊄? t

_≐_ : Rel St ℓa
t ≐ u = ⟦ t ⟧ U.≐ ⟦ u ⟧
_≐?_ : Binary.Decidable _≐_
t ≐? u = t ⊆? u ×-dec u ⊆? t

_≬_ : Rel St ℓa
t ≬ u = ⟦ t ⟧ U.≬ ⟦ u ⟧
_≬?_ : Binary.Decidable _≬_
t ≬? u = Nullary.map (U.≐→Satisfiable⇔ (⟦∩⟧ t u)) (Satisfiable? (t ∩ u))

∈→Any : ∀ {ℓ} → {P : Pred Key ℓ} → {k : Key} → {t : St} → (P Respects _≈_) →
        P k → k ∈ t → Any P t
∈→Any resp Pk k∈t =
  lookup-rebuild k∈t (resp (lookup-result k∈t) Pk)
Any→∈ : ∀ {ℓ} → {P : Pred Key ℓ} → {t : St} →
        Any P t → Σ[ k ∈ Key ] k ∈ t × P k
Any→∈ {P = P} {t = t} path =
  let k = Any.lookupKey path
      k∈t = lookup-rebuild path Eq.refl
      Pk = lookup-result {P = P ∘ key} path
  in k , k∈t , Pk
Any⇔∈ : ∀ {ℓ} → {P : Pred Key ℓ} → (P Respects _≈_) → (t : St) →
        Any P t ⇔ (Σ[ k ∈ Key ] k ∈ t × P k)
Any⇔∈ resp t = mk⇔ Any→∈ λ{ (k , k∈t , Pk) → ∈→Any {k = k} resp Pk k∈t}

infix 4 _Lex<_ _≐-onList_
-- Lexicographic order on `toList`.
_Lex<_ : Rel St ℓa
_Lex<_ = (ListLex.Lex-< _≈_ _<_) on toList
_≐-onList_ : Rel St ℓa
_≐-onList_ = Pointwise _≈_ on toList
≐-onList⇒≐ : _≐-onList_ Binary.⇒ _≐_
≐-onList⇒≐ {t} {u} xs=ys = begin
  ⟦ t ⟧
    ≈⟨ U.≐-sym (⟦toList⟧ t) ⟩
  ListMem._∈ (toList t)
    ≈⟨ Pointwise→∈ xs=ys ⟩
  ListMem._∈ (toList u)
    ≈⟨ ⟦toList⟧ u ⟩
  ⟦ u ⟧ ∎
  where open ≐-Reasoning
≐⇒≐-onList : _≐_ Binary.⇒ _≐-onList_
≐⇒≐-onList {t} {u} t≐u =
  StrictSorted-≐→Pointwise (toList-StrictSorted t) (toList-StrictSorted u) ∈List≐
  where
  open ≐-Reasoning
  ∈List≐ : (ListMem._∈ (toList t)) U.≐ (ListMem._∈ (toList u))
  ∈List≐ = begin
    (ListMem._∈ (toList t))
      ≈⟨ ⟦toList⟧ t ⟩
    ⟦ t ⟧
      ≈⟨ t≐u ⟩
    ⟦ u ⟧
      ≈⟨ U.≐-sym (⟦toList⟧ u) ⟩
    (ListMem._∈ (toList u)) ∎
≐-onList⇔≐ : _≐-onList_ Binary.⇔ _≐_
≐-onList⇔≐ = ≐-onList⇒≐ , ≐⇒≐-onList
{-
lex-isStrictTotalOrder is the lexicographic order on `toList`, which is the sorted list of Keys.
This reduces to List's Lexicographic isStrictTotalOrder.
This needs ≐-onList⇔≐ to show that List's pointwise equivalence is equivalent to _≐_.
-}
lex-isStrictTotalOrder : IsStrictTotalOrder _≐_ _Lex<_
lex-isStrictTotalOrder = Equality.isStrictTotalOrder ≐-onList⇔≐ onListIsSTO
  where
  listIsSTO : IsStrictTotalOrder (Pointwise _≈_) (ListLex.Lex-< _≈_ _<_)
  listIsSTO = ListLexStrict.<-isStrictTotalOrder STO.isStrictTotalOrder
  onListIsSTO : IsStrictTotalOrder _≐-onList_ _Lex<_
  onListIsSTO = On.isStrictTotalOrder toList listIsSTO
lex-strictTotalOrder : StrictTotalOrder ℓa ℓa ℓa
lex-strictTotalOrder = record { isStrictTotalOrder = lex-isStrictTotalOrder }

≐-refl : Reflexive {A = St} _≐_
≐-refl = U.≐-refl
≐-sym : Symmetric {A = St} _≐_
≐-sym tu = U.≐-sym tu
≐-trans : Transitive {A = St} _≐_
≐-trans tu uv = U.≐-trans tu uv
≐-isEquivalence : IsEquivalence _≐_
≐-isEquivalence = record
  { refl = ≐-refl
  ; sym = ≐-sym
  ; trans = ≐-trans }
⊂-irrefl : Irreflexive _≐_ _⊂_
⊂-irrefl = U.⊂-irrefl
⊂-trans : Transitive _⊂_
⊂-trans = U.⊂-trans
⊂-⊆-trans : Trans _⊂_ _⊆_ _⊂_
⊂-⊆-trans = U.⊂-⊆-trans
⊆-⊂-trans : Trans _⊆_ _⊂_ _⊂_
⊆-⊂-trans = U.⊆-⊂-trans
⊂-respʳ-≐ : _Respectsʳ_ _⊂_ _≐_
⊂-respʳ-≐ = U.⊂-respʳ-≐
⊂-respˡ-≐ : _Respectsˡ_ _⊂_ _≐_
⊂-respˡ-≐ = U.⊂-respˡ-≐
⊂-resp-≐ : _Respects₂_ _⊂_ _≐_
⊂-resp-≐ = ⊂-respʳ-≐ , ⊂-respˡ-≐

⊂-isStrictPartialOrder : IsStrictPartialOrder _≐_ _⊂_
⊂-isStrictPartialOrder = record
  { isEquivalence = ≐-isEquivalence
  ; irrefl = ⊂-irrefl
  ; trans = ⊂-trans
  ; <-resp-≈ = ⊂-resp-≐ }
⊂-strictPartialOrder : StrictPartialOrder ℓa ℓa ℓa
⊂-strictPartialOrder = record { isStrictPartialOrder = ⊂-isStrictPartialOrder }

{-
TODO: This needs to be in another file for different elem types.
powerSet : St → St
powerSet t = {!!}
⟦powerSet⟧ : (t : St) → ⟦ powerSet t ⟧ U.≐ (_⊆ t)
⟦powerSet⟧ = ?
-}
