{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (StrictTotalOrder)

module Ponens.Data.Tree.AVL.Indexed.Properties.Lookup
  {a ℓ₁ ℓ₂} (sto : StrictTotalOrder a ℓ₁ ℓ₂) where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (nothing; just)
import Data.Maybe.Relation.Unary.Any as Maybe
open import Data.Nat using (zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax; ∃)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_; _⇔_; Equivalence)
open import Level using (Level; _⊔_)
open import Ponens.Relation.Unary.Properties using (Maybe-right-unique→≐)
open import Relation.Binary using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Relation.Nullary using (¬_)
open import Relation.Unary using (Pred; _≐_)

open import Data.Tree.AVL.Indexed sto using (Tree; leaf; node; Value; K&_; key; _,_; _<_<_)
open import Data.Tree.AVL.Indexed.Relation.Unary.Any sto as Any using (Any; here; left; right)
open import Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties sto using (lookup-result; lookup-rebuild)
open import Ponens.Data.Tree.AVL.Indexed sto using (head; lookup->)
open import Ponens.Data.Tree.AVL.Indexed.Properties.Any sto using (_∈_; node-¬Any; just-≐→⇔)
open import Ponens.Data.Tree.AVL.Indexed.Properties.HeadTail sto using (head-cases)
open import Ponens.Data.Tree.AVL.Indexed.Properties.Gap sto using (Gap; Gap-∈; ∈-compare; _<-∈_; ∈→<u; ∈→l<; ¬k<u→¬<; ¬k1<u→¬gap; ¬l<k2→¬gap)

module STO = StrictTotalOrder sto
open STO using (module Eq; _<_; compare) renaming (Carrier to Key)
open import Relation.Binary.Construct.Add.Extrema.Strict _<_ using ([_])
import Relation.Binary.Reasoning.StrictPartialOrder STO.strictPartialOrder as SPO-Reasoning

private
  variable
    v p : Level
    V : Value v
    P : Pred (K& V) p

lookup->-cases : ∀ {l u h} (t : Tree V l u h) (k : Key) (l<k<u : l < k < u) →
              (  lookup-> {V = V} t k l<k<u ≡ nothing
               × ¬ (k <-∈ t))
            ⊎ (∃ λ r → (lookup-> {V = V} t k l<k<u ≡ just r)
                     × (r ∈ t)
                     × k < key r
                     × ¬ Gap-∈ k (key r) t)
lookup->-cases {h = zero} (leaf l<u) k (l<k , k<u) = inj₁ (refl , λ ())
lookup->-cases {h = suc h} (node (k′ , v) lk′ k′u bal) k (l<k , k<u) with compare k′ k
lookup->-cases {V = V} {h = suc h} t@(node (k′ , v) lk′ k′u bal) k (l<k , k<u) | tri< k′<k _ ¬k<k′ with lookup-> k′u k ([ k′<k ] , k<u) | lookup->-cases k′u k ([ k′<k ] , k<u)
... | nothing | inj₁ (refl , ¬<k′u) =
  inj₁ (refl , ¬k<t)
  where
  ¬k<t : ¬ (k <-∈ t)
  ¬k<t = node-¬Any ¬k<k′ (¬k<u→¬< lk′ ¬k<k′) ¬<k′u
... | just (rk , rv) | inj₂ ((.rk , .rv) , refl , ih-∈ , ih-k<r , ¬gap-k′u) =
  inj₂ ((rk , rv) , refl , right ih-∈ , ih-k<r , ¬gap)
  where
  ¬gap : ¬ Gap-∈ k rk t
  ¬gap = node-¬Any (¬k<k′ ∘ proj₁)
                   (¬k1<u→¬gap k rk lk′ ¬k<k′)
                   ¬gap-k′u
lookup->-cases {V = V} {u = u} {h = suc h} t@(node (k′ , v) lk′ k′u bal) k (l<k , k<u) | tri≈ _ k′≈k ¬k<k′ with head {V = V} k′u | head-cases {V = V} k′u
... | nothing | inj₁ (refl , ¬<k′u) =
  inj₁ (refl , ¬k<t)
  where
  ¬k<t : ¬ (k <-∈ t)
  ¬k<t = node-¬Any ¬k<k′ (¬k<u→¬< lk′ ¬k<k′) (¬<k′u k)
... | just (rk , rv) | inj₂ ((.rk , .rv) , refl , r∈ , ¬<k′u) =
  inj₂ ((rk , rv) , refl , right r∈ , k<rk , ¬gap)
  where
  open SPO-Reasoning
  k<rk : k < rk
  k<rk = begin-strict
         k ≈⟨ Eq.sym k′≈k ⟩
         k′ <⟨ ∈→l< r∈ ⟩
         rk ∎
  ¬gap : ¬ Gap-∈ k rk t
  ¬gap = node-¬Any (¬k<k′ ∘ proj₁)
                   (¬k1<u→¬gap k rk lk′ ¬k<k′)
                   (¬<k′u ∘ Any.map proj₂)
lookup->-cases {V = V} {l = l} {u} {h = suc h} t@(node (k′ , v) lk′ k′u bal) k (l<k , k<u) | tri> ¬k′<k _ k<k′ with lookup-> lk′ k (l<k , [ k<k′ ]) | lookup->-cases lk′ k (l<k , [ k<k′ ])
... | nothing | inj₁ (refl , ¬<lk′) =
  inj₂ ((k′ , v) , refl , here refl , k<k′ , ¬gap)
  where
  ¬k′<k′ : ¬ k′ < k′
  ¬k′<k′ = STO.irrefl Eq.refl
  ¬gap : ¬ Gap-∈ k k′ t
  ¬gap = node-¬Any (¬k′<k′ ∘ proj₂)
                   (¬<lk′ ∘ Any.map proj₁)
                   (¬l<k2→¬gap k k′ k′u ¬k′<k′)
... | just (rk , rv) | inj₂ ((.rk , .rv) , refl , r∈ , ih-bound , ¬gap-lk′) =
  inj₂ ((rk , rv) , refl , left r∈ , ih-bound , ¬gap)
  where
  ¬k′<rk : ¬ k′ < rk
  ¬k′<rk = STO.asym (∈→<u r∈)
  ¬gap : ¬ Gap-∈ k rk t
  ¬gap = node-¬Any (¬k′<rk ∘ proj₂)
                   (¬gap-lk′)
                   (¬l<k2→¬gap k rk k′u ¬k′<rk)

conflicting-¬gaps : ∀ {l u h} {t : Tree V l u h} {k : Key}
      (kv1 kv2 : K& V) →
      kv1 ∈ t → k < key kv1 → key kv1 < key kv2 → ¬ Any (λ kv → Gap k (key kv2) (key kv)) t →
      ⊥
conflicting-¬gaps {k = k} kv1 kv2 p1 k<kv1 kv1<kv2 ¬gap2 =
    (¬gap2 (lookup-rebuild p1
             (subst
               (Gap k (key kv2) ∘ key)
               (lookup-result p1)
               (k<kv1 , kv1<kv2))))

lookup->-≡ : ∀ {l u h} (t : Tree V l u h) (k : Key)
      (kv1 kv2 : K& V) →
      (kv1 ∈ t) × k < key kv1 × ¬ Gap-∈ k (key kv1) t →
      (kv2 ∈ t) × k < key kv2 × ¬ Gap-∈ k (key kv2) t →
      kv1 ≡ kv2
lookup->-≡ t k kv1 kv2 (p1 , k<kv1 , ¬gap1) (p2 , k<kv2 , ¬gap2) with ∈-compare p1 p2
... | tri< kv1<kv2 ¬b ¬c = ⊥-elim (conflicting-¬gaps kv1 kv2 p1 k<kv1 kv1<kv2 ¬gap2)
... | tri≈ _ eq _ = eq
... | tri> ¬a ¬b c = ⊥-elim (conflicting-¬gaps kv2 kv1 p2 k<kv2 c ¬gap1)

lookup->-Result : {V : Value v} → ∀ {l u h} (t : Tree V l u h) (k : Key) → Pred (K& V) (a ⊔ ℓ₂ ⊔ v)
lookup->-Result t k kv = (kv ∈ t) × k < key kv × ¬ Gap-∈ k (key kv) t

lookup->-≐ : ∀ {l u h} (t : Tree V l u h) (k : Key) (l<k<u : l < k < u) →
     (λ r → lookup-> {V = V} t k l<k<u ≡ just r)
     ≐ (λ r → lookup->-Result t k r)
lookup->-≐ {V = V} t k l<k<u =
  Maybe-right-unique→≐
    (lookup->-cases {V = V} t k l<k<u)
    (λ{ r (r∈t , k<r , _) ¬k<t → ¬k<t (Any.map (λ{ refl → k<r}) r∈t)})
    (lookup->-≡ t k)

-- TODO: Remove the following if unused.
lookup->-nothing⁻ : ∀ {l u h} (t : Tree V l u h) (k : Key) (l<k<u : l < k < u) →
                   lookup-> t k l<k<u ≡ nothing →
                   ¬ (k <-∈ t)
lookup->-nothing⁻ t k l<k<u eq with lookup->-cases t k l<k<u
lookup->-nothing⁻ t k l<k<u eq | inj₁ (_ , ¬<t) = ¬<t
lookup->-nothing⁻ t k l<k<u eq | inj₂ (r , eq-just , _) rewrite eq with eq-just
...   | ()
lookup->-just⁻ : ∀ {l u h} (t : Tree V l u h) (k : Key) (l<k<u : l < k < u) →
                (r : K& V) → lookup-> t k l<k<u ≡ just r →
                (r ∈ t) × k < key r × ¬ Gap-∈ k (key r) t
lookup->-just⁻ t k l<k<u r eq with lookup->-cases t k l<k<u
lookup->-just⁻ t k l<k<u r eq | inj₁ (eq-nothing , _) rewrite eq with eq-nothing
...   | ()
lookup->-just⁻ t k l<k<u r eq | inj₂ (r′ , eq-just , r∈t , k<r , ¬gap) rewrite eq with eq-just
...   | refl = r∈t , k<r , ¬gap

lookup->-⇔ : ∀ {l u h} (t : Tree V l u h) (k : Key) (l<k<u : l < k < u) →
               Maybe.Any P (lookup-> t k l<k<u)
               ⇔ (Σ[ path ∈ Any P t ] k < Any.lookupKey path × ¬ Gap-∈ k (Any.lookupKey path) t)
lookup->-⇔ t k l<k<u =
  just-≐→⇔ (lookup->-≐ t k l<k<u)

lookup->⁻ : ∀ {l u h} (t : Tree V l u h) (k : Key) (l<k<u : l < k < u) →
                    Maybe.Any P (lookup-> t k l<k<u) →
                    Σ[ path ∈ Any P t ] k < Any.lookupKey path × ¬ Gap-∈ k (Any.lookupKey path) t
lookup->⁻ t k l<k<u =
  Equivalence.to (lookup->-⇔ t k l<k<u)

lookup->⁺ : ∀ {l u h} (t : Tree V l u h) (k : Key) (l<k<u : l < k < u) →
                    (path : Any P t) → k < Any.lookupKey path → ¬ Gap-∈ k (Any.lookupKey path) t →
                    Maybe.Any P (lookup-> t k l<k<u)
lookup->⁺ t k l<k<u path k<path ¬gap =
  Equivalence.from (lookup->-⇔ t k l<k<u) (path , k<path , ¬gap)
