{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (StrictTotalOrder)

module Ponens.Data.Tree.AVL.Indexed.Properties.Gap
  {a ℓ₁ ℓ₂} (sto : StrictTotalOrder a ℓ₁ ℓ₂) where

open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Function using (_∘_)
open import Level using (Level; _⊔_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary using (Tri; tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym)

open import Data.Tree.AVL.Indexed sto using (Tree; node; Value; K&_; key; Key⁺; [_])
open import Data.Tree.AVL.Indexed.Relation.Unary.Any sto as Any using (Any; here; left; right)
open import Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties sto using (lookup-result; lookup-bounded)
open import Ponens.Data.Tree.AVL.Indexed.Properties.Any sto using (_∈_; ∈-bounded)

module STO = StrictTotalOrder sto
open STO using (module Eq; _≈_; _<_) renaming (Carrier to Key)
open import Relation.Binary.Construct.Add.Extrema.Strict _<_ using ([<]-injective)

-- Gap k1 k2 mid = [ k1 ] < mid < [ k2 ]
Gap : (k1 k2 mid : Key) → Set ℓ₂
Gap k1 k2 mid = (k1 < mid) × (mid < k2)

Gap-cong₁ : {k1 k1′ k2 mid : Key} → Gap k1 k2 mid → (k1 ≈ k1′) → Gap k1′ k2 mid
Gap-cong₁ (k1<mid , mid<k2) eq = STO.<-respˡ-≈ eq k1<mid , mid<k2
Gap-cong₂ : {k1 k2 k2′ mid : Key} → Gap k1 k2 mid → (k2 ≈ k2′) → Gap k1 k2′ mid
Gap-cong₂ (k1<mid , mid<k2) eq = k1<mid , STO.<-respʳ-≈ eq mid<k2

module _ {v : Level} {V : Value v} where
  Gap-∈ : (k1 k2 : Key) →
          ∀ {l u h} (t : Tree V l u h) → Set (a ⊔ ℓ₂ ⊔ v)
  Gap-∈ k1 k2 t = Any (Gap k1 k2 ∘ key) t
  _<-∈_ : (k : Key) →
          ∀ {l u h} (t : Tree V l u h) → Set (a ⊔ ℓ₂ ⊔ v)
  _<-∈_ k t = Any ((k <_) ∘ key) t
  _>-∈_ : (k : Key) →
          ∀ {l u h} (t : Tree V l u h) → Set (a ⊔ ℓ₂ ⊔ v)
  _>-∈_ k t = Any ((_< k) ∘ key) t

  ¬k<u→¬< : ∀ {k l u h} (t : Tree V l [ u ] h) → ¬ k < u → ¬ k <-∈ t
  ¬k<u→¬< t ¬k<u k<t =
    ¬k<u (STO.trans (lookup-result k<t)
                    ([<]-injective (proj₂ (lookup-bounded k<t))))
  ¬l<k→¬< : ∀ {k l u h} (t : Tree V [ l ] u h) → ¬ l < k → ¬ k >-∈ t
  ¬l<k→¬< t ¬l<k t<k =
    ¬l<k (STO.trans ([<]-injective (proj₁ (lookup-bounded t<k)))
                    (lookup-result t<k))

  ¬k1<u→¬gap : (k1 k2 : Key) → ∀ {l u h} (t : Tree V l [ u ] h) → ¬ k1 < u → ¬ Gap-∈ k1 k2 t
  ¬k1<u→¬gap k1 k2 t ¬k1<u =
    ¬k<u→¬< t ¬k1<u ∘ Any.map proj₁
  ¬l<k2→¬gap : (k1 k2 : Key) → ∀ {l u h} (t : Tree V [ l ] u h) → ¬ l < k2 → ¬ Gap-∈ k1 k2 t
  ¬l<k2→¬gap k1 k2 t ¬l<k2 =
    ¬l<k→¬< t ¬l<k2 ∘ Any.map proj₂

  ∈→<u : ∀ {kv} → ∀ {l u h} {t : Tree V l [ u ] h} → kv ∈ t → key kv < u
  ∈→<u kv∈ = [<]-injective (proj₂ (∈-bounded kv∈))
  ∈→l< : ∀ {kv} → ∀ {l u h} {t : Tree V [ l ] u h} → kv ∈ t → l < key kv
  ∈→l< kv∈ = [<]-injective (proj₁ (∈-bounded kv∈))

  ∈→≢u : {l : Key⁺} {u : K& V} {h : ℕ} {t : Tree V l [ key u ] h} → {kv : K& V} → kv ∈ t → kv ≢ u
  ∈→≢u kv∈t refl = STO.irrefl Eq.refl (∈→<u kv∈t)
  ∈→≢l : {l : K& V} {u : Key⁺} {h : ℕ} {t : Tree V [ key l ] u h} → {kv : K& V} → kv ∈ t → l ≢ kv
  ∈→≢l kv∈t refl = STO.irrefl Eq.refl (∈→l< kv∈t)

  ∈-∈→< : ∀ {l u hˡ hʳ} (m : K& V) {lm : Tree V l [ key m ] hˡ} {mu : Tree V [ key m ] u hʳ} →
       {kv1 kv2 : K& V} → kv1 ∈ lm → kv2 ∈ mu → key kv1 < key kv2
  ∈-∈→< m kv1∈lm kv2∈mu = STO.trans (∈→<u kv1∈lm) (∈→l< kv2∈mu)
  ∈-∈→≢ : ∀ {l u hˡ hʳ} (m : K& V) {lm : Tree V l [ key m ] hˡ} {mu : Tree V [ key m ] u hʳ} →
       {kv1 kv2 : K& V} → kv1 ∈ lm → kv2 ∈ mu → kv1 ≢ kv2
  ∈-∈→≢ m kv1∈lm kv2∈mu refl =
    STO.irrefl Eq.refl (∈-∈→< m kv1∈lm kv2∈mu)
  ∈-∈→≮ : ∀ {l u hˡ hʳ} (m : K& V) {lm : Tree V l [ key m ] hˡ} {mu : Tree V [ key m ] u hʳ} →
       {kv1 kv2 : K& V} → kv1 ∈ lm → kv2 ∈ mu → ¬ key kv2 < key kv1
  ∈-∈→≮ m kv1∈lm kv2∈mu = STO.asym (∈-∈→< m kv1∈lm kv2∈mu)

  K&-irrefl : (kv : K& V) → ¬ key kv < key kv
  K&-irrefl kv = STO.irrefl Eq.refl
  ∈→u≮ : {l : Key⁺} (u : K& V) {h : ℕ} {t : Tree V l [ key u ] h} → {kv : K& V} → kv ∈ t → ¬ key u < key kv
  ∈→u≮ u kv∈t = STO.asym (∈→<u kv∈t)
  ∈→≮l : (l : K& V) {u : Key⁺} {h : ℕ} {t : Tree V [ key l ] u h} → {kv : K& V} → kv ∈ t → ¬ key kv < key l
  ∈→≮l l kv∈t = STO.asym (∈→l< kv∈t)

  ∈-compare : ∀ {l u h} {t : Tree V l u h} →
              {kv1 kv2 : K& V} → kv1 ∈ t → kv2 ∈ t →
              Tri (key kv1 < key kv2) (kv1 ≡ kv2) (key kv2 < key kv1)
  ∈-compare {kv1 = kv1} (here refl) (here refl) =
    tri≈ (K&-irrefl kv1) refl (K&-irrefl kv1)
  ∈-compare {kv1 = kv1} {kv2 = kv2} (left p1) (left p2) =
    ∈-compare p1 p2
  ∈-compare {kv1 = kv1} {kv2 = kv2} (right p1) (right p2) =
    ∈-compare p1 p2
  ∈-compare {kv1 = kv1} {kv2 = kv2} (here refl) (left p2) =
    tri> (∈→u≮ kv1 p2) (∈→≢u p2 ∘ sym) (∈→<u p2)
  ∈-compare {kv1 = kv1} {kv2 = kv2} (left p1) (here refl) =
    tri< (∈→<u p1) (∈→≢u p1) (∈→u≮ kv2 p1)
  ∈-compare {kv1 = kv1} {kv2 = kv2} (here refl) (right p2) =
    tri< (∈→l< p2) (∈→≢l p2) (∈→≮l kv1 p2)
  ∈-compare {kv1 = kv1} {kv2 = kv2} (right p1) (here refl) =
    tri> (∈→≮l kv2 p1) (∈→≢l p1 ∘ sym) (∈→l< p1)
  ∈-compare {t = node kv _ _ _} {kv1 = kv1} {kv2 = kv2} (left p1) (right p2) =
    tri< (∈-∈→< kv p1 p2) (∈-∈→≢ kv p1 p2) (∈-∈→≮ kv p1 p2)
  ∈-compare {t = node kv _ _ _} {kv1 = kv1} {kv2 = kv2} (right p1) (left p2) =
    tri> (∈-∈→≮ kv p2 p1) (∈-∈→≢ kv p2 p1 ∘ sym) (∈-∈→< kv p2 p1)

  -- TODO: Define the Trichotomous and use tri⇒dec≈.
  ∈-≟ : ∀ {l u h} {t : Tree V l u h} →
        {kv1 kv2 : K& V} → kv1 ∈ t → kv2 ∈ t → Dec (kv1 ≡ kv2)
  ∈-≟ p1 p2 with ∈-compare p1 p2
  ... | tri< _ ¬eq _ = no ¬eq
  ... | tri≈ _ eq _ = yes eq
  ... | tri> _ ¬eq _ = no ¬eq
