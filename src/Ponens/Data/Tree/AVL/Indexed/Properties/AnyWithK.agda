{-
TODO: Move properties here to Any.
-}
{-# OPTIONS --with-K --safe #-}

open import Relation.Binary.Bundles using (StrictTotalOrder)

module Ponens.Data.Tree.AVL.Indexed.Properties.AnyWithK
  {a ℓ₁ ℓ₂} (sto : StrictTotalOrder a ℓ₁ ℓ₂) where

open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_; proj₁; proj₂; Σ-syntax)
open import Function using (_∘_; _on_; Congruent; Inverse)
open import Level using (Level; _⊔_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; refl; sym; trans; subst; cong)
open import Relation.Unary using (Pred)
open import Ponens.Data.Product.Properties using (proj₁-setoid)

open import Data.Tree.AVL.Indexed sto using (Tree; node; Value; K&_; key; Key⁺)
open import Data.Tree.AVL.Indexed.Relation.Unary.Any sto as Any using (Any; here; left; right)
open import Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties sto using (lookup-result; lookup-bounded)
open import Ponens.Data.Tree.AVL.Indexed.Properties.Any sto using (_∈_; _∈k_; Any→∈; Any→Σ∈; key-lookup; lookup-∈k)

module STO = StrictTotalOrder sto
open STO using (module Eq; _≈_; _<_) renaming (Carrier to Key)
open Eq using (setoid)
open import Relation.Binary.Construct.Add.Extrema.Strict _<_ using ([<]-injective)

module _ {v : Level} {V : Value v} where
  Any→∈-unique : {p : Level} {P : Pred (K& V) p} →
                 ∀ {l u h} {t : Tree V l u h} (path : Any P t) (kv∈t : Any.lookup path ∈ t) →
                 Any→∈ path ≡ kv∈t
  Any→∈-unique (here _) (here refl) = refl
  Any→∈-unique {t = node kv lk ku bal} (here path) (left kv∈t) =
    ⊥-elim (STO.irrefl
      (subst (λ kv′ → key kv′ ≈ key kv) (lookup-result kv∈t) Eq.refl)
      ([<]-injective (proj₂ (lookup-bounded kv∈t))))
  Any→∈-unique {t = node kv lk ku bal} (here path) (right kv∈t) =
    ⊥-elim (STO.irrefl
      (subst (λ kv′ → key kv ≈ key kv′) (lookup-result kv∈t) Eq.refl)
      (([<]-injective (proj₁ (lookup-bounded kv∈t)))))
  Any→∈-unique {t = node kv lk ku bal} (left path) (here kv∈t) =
    ⊥-elim (STO.irrefl
      (subst (λ kv′ → key kv′ ≈ key kv) (sym kv∈t) Eq.refl)
      ([<]-injective (proj₂ (lookup-bounded path))))
  Any→∈-unique (left path) (left kv∈t) = cong (λ path′ → left path′) (Any→∈-unique path kv∈t)
  Any→∈-unique {t = node kv lk ku bal} (left path) (right kv∈t) =
    ⊥-elim (STO.irrefl
      (subst (λ kv′ → key (Any.lookup path) ≈ key kv′) (lookup-result kv∈t) Eq.refl)
      (STO.trans ([<]-injective (proj₂ (lookup-bounded path))) ([<]-injective (proj₁ (lookup-bounded kv∈t)))))
  Any→∈-unique {t = node kv lk ku bal} (right path) (here kv∈t) =
    ⊥-elim (STO.irrefl
      (subst (λ kv′ → key kv ≈ key kv′) (sym kv∈t) Eq.refl)
      ([<]-injective (proj₁ (lookup-bounded path))))
  Any→∈-unique {t = node kv lk ku bal} (right path) (left kv∈t) =
    ⊥-elim (STO.irrefl
      (subst (λ kv′ → key kv′ ≈ key (Any.lookup path)) (lookup-result kv∈t) Eq.refl)
      (STO.trans ([<]-injective (proj₂ (lookup-bounded kv∈t))) ([<]-injective (proj₁ (lookup-bounded path)))))
  Any→∈-unique (right path) (right kv∈t) = cong (λ path′ → right path′) (Any→∈-unique path kv∈t)

-- Functions that implicitly depend on a Tree.
module _ {v : Level} {V : Value v}
         {l u : Key⁺} {h : ℕ} {t : Tree V l u h} where

  k≈kv→Σ∈ : {k : Key} (k∈t : k ∈k t) {kv : K& V} (kv∈t : kv ∈ t) →
            k ≈ key kv → Any→Σ∈ k∈t ≡ (kv , kv∈t)
  k≈kv→Σ∈ {k = k} k∈t {kv} kv∈t eq with lookup-∈k k∈t kv∈t eq
  ... | refl = cong (Any.lookup k∈t ,_) (Any→∈-unique k∈t kv∈t)

  k≈k→Σ∈ : {k1 k2 : Key} (k1∈t : k1 ∈k t) (k2∈t : k2 ∈k t) →
           (k1 ≈ k2) → Any→Σ∈ k1∈t ≡ Any→Σ∈ k2∈t
  k≈k→Σ∈ {k1} k1∈t k2∈t eq =
    let (kv , kv∈t) = Any→Σ∈ k1∈t
        k1≈kv : k1 ≈ key kv
        k1≈kv = Eq.sym (key-lookup k1∈t)
    in trans (k≈kv→Σ∈ k1∈t kv∈t k1≈kv)
            (sym (k≈kv→Σ∈ k2∈t kv∈t (Eq.trans (Eq.sym eq) k1≈kv)))

module _ {v : Level} {V : Value v}
         {l u : Key⁺} {h : ℕ} where
  KV-Inverse-Key : (t : Tree V l u h) →
                   Inverse (≡.setoid (Σ[ kv ∈ K& V ] Any (kv ≡_) t))
                           (proj₁-setoid setoid λ k → Any ((k ≈_) ∘ key) t)
  KV-Inverse-Key t = record
    { to = f
    ; from = g
    ; to-cong = f-cong
    ; from-cong = g-cong
    ; inverse = inv-l , inv-r }
    where
    f-eq : (kv : K& V) {kv′ : K& V} → kv ≡ kv′ → key kv ≈ key kv′
    f-eq kv refl = Eq.refl
    f : (Σ[ kv ∈ K& V ] Any (kv ≡_) t) → (Σ[ k ∈ Key ] Any ((k ≈_) ∘ key) t)
    f (kv , path) = key kv , Any.map (f-eq kv) path
    g : (Σ[ k ∈ Key ] Any ((k ≈_) ∘ key) t) → (Σ[ kv ∈ K& V ] Any (kv ≡_) t)
    g (k , path) = Any.lookup path , Any→∈ path
    f-cong : Congruent _≡_ (_≈_ on proj₁) f
    f-cong refl = Eq.refl
    g-cong : Congruent (_≈_ on proj₁) _≡_ g
    g-cong {_ , k1∈t} {_ , k2∈t} = k≈k→Σ∈ k1∈t k2∈t
    inv-l : ∀ {x y} → y ≡ g x → proj₁ (f y) ≈ proj₁ x
    inv-l {_ , k∈t} {_} refl = key-lookup k∈t
    inv-r : ∀ {x y} → proj₁ y ≈ proj₁ (f x) → g y ≡ x
    inv-r {_ , kv∈t} {_ , k∈t} = k≈kv→Σ∈ k∈t kv∈t
