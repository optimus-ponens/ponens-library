{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (StrictTotalOrder)

module Ponens.Data.Tree.AVL.Indexed.Properties.Any
  {a ℓ₁ ℓ₂} (sto : StrictTotalOrder a ℓ₁ ℓ₂) where

open import Data.Empty using (⊥-elim)
open import Data.Maybe using (Maybe; just)
open import Data.Maybe.Relation.Unary.Any as Maybe using (just)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ; Σ-syntax; curry; uncurry)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_; _⇔_; _↔_; mk⇔; mk↔)
open import Level using (Level; _⊔_)
open import Ponens.Data.Maybe.Relation.Unary.Any.Properties using (just→Any)
open import Ponens.Function.Related.TypeIsomorphisms using (Preds↔⊎3→∃↔⊎3)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import Relation.Nullary.Negation using (¬_; contradiction)
open import Relation.Unary using (Pred; _≐_; _∩_)

open import Data.Tree.AVL.Indexed sto using (Tree; node; Value; K&_; key; Key⁺; [_]; _∼_⊔_; _<_<_)
open import Data.Tree.AVL.Indexed.Relation.Unary.Any sto as Any using (Any; here; left; right; toSum; fromSum; lookupKey)
open import Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties sto using (lookup-result; lookup-bounded; lookup-rebuild)
open import Ponens.Data.Tree.AVL.Indexed.Properties.Range sto using (bounds-resp-≈)

module STO = StrictTotalOrder sto
open STO using (module Eq; _≈_; _<_) renaming (Carrier to Key)
open Eq using (_≉_)
open import Relation.Binary.Construct.Add.Extrema.Strict _<_ using ([<]-injective)

module _ {v : Level} {V : Value v} where
  -- TODO: Is this the fully general dependent eliminator?
  Any-elim :
    {p : Level} {P : Pred (K& V) p}
    {q : Level} (Q : ∀ {l u n} {t : Tree V l u n} (path : Any P t) → Set q) →
          (∀ {l u} → ∀ {hˡ hʳ h} {kv : K& V} → (Pkv : P kv) →
             {lk : Tree V l [ key kv ] hˡ}
             {ku : Tree V [ key kv ] u hʳ}
             {bal : hˡ ∼ hʳ ⊔ h} →
             Q (here Pkv {lk = lk} {ku = ku} {bal = bal})) →
          (∀ {l u} → ∀ {hˡ hʳ h} {kv : K& V}
             {lk : Tree V l [ key kv ] hˡ} →
             (path : Any P lk) →
             {ku : Tree V [ key kv ] u hʳ}
             {bal : hˡ ∼ hʳ ⊔ h} →
             Q path →
             Q (left {kv = kv} path {ku = ku} {bal = bal})) →
          (∀ {l u} → ∀ {hˡ hʳ h} {kv : K& V}
             {lk : Tree V l [ key kv ] hˡ}
             {ku : Tree V [ key kv ] u hʳ} →
             (path : Any P ku) →
             {bal : hˡ ∼ hʳ ⊔ h} →
             Q path →
             Q (right {kv = kv} {lk = lk} path {bal = bal})) →
          ∀ {l u n} {t : Tree V l u n} →
          (path : Any P t) → Q path
  Any-elim _ f-here f-left f-right (here Pkv) =
    f-here Pkv
  Any-elim Q f-here f-left f-right (left path) =
    f-left path (Any-elim Q f-here f-left f-right path)
  Any-elim Q f-here f-left f-right (right path) =
    f-right path (Any-elim Q f-here f-left f-right path)

  Any-fold : {p : Level} {P : Pred (K& V) p}
             {q : Level} {Q : Set q} →
            ({kv : K& V} → P kv → Q) →
            (∀ {l u h} {t : Tree V l u h} → Any P t → Q → Q) →
            (∀ {l u h} {t : Tree V l u h} → Any P t → Q → Q) →
            ∀ {l u h} {t : Tree V l u h} →
            Any P t → Q
  Any-fold {Q = Q} f-here f-left f-right path =
    Any-elim (λ _ → Q)
      (λ Pkv → f-here Pkv)
      (λ path → f-left path)
      (λ path → f-right path)
      path

-- functions on `node`s
module _ {v : Level} {V : Value v}
         {l u : Key⁺}
         {hˡ hʳ h : ℕ} {kv : K& V}
         {lk : Tree V l [ key kv ] hˡ}
         {ku : Tree V [ key kv ] u hʳ}
         {bal : hˡ ∼ hʳ ⊔ h} where

  Any↔⊎ : {p : Level} {P : Pred (K& V) p} →
          Any P (node kv lk ku bal) ↔ (P kv ⊎ Any P lk ⊎ Any P ku)
  Any↔⊎ = mk↔ {to = toSum} {from = fromSum}
     ((λ{ {inj₁ _} refl → refl
        ; {inj₂ (inj₁ _)} refl → refl
        ; {inj₂ (inj₂ _)} refl → refl })
    , λ{ {here p} {inj₁ .p} refl → refl
       ; {left p} {inj₂ (inj₁ .p)} refl → refl
       ; {right p} {inj₂ (inj₂ .p)} refl → refl})

  ∈↔⊎ : (Σ[ kv' ∈ K& V ] (Any (kv' ≡_) (node kv lk ku bal)))
        ↔ ((Σ[ kv' ∈ K& V ] kv' ≡ kv)
          ⊎ (Σ[ kv' ∈ K& V ] (Any (kv' ≡_) lk))
          ⊎ (Σ[ kv' ∈ K& V ] (Any (kv' ≡_) ku)))
  ∈↔⊎ = Preds↔⊎3→∃↔⊎3 λ a → Any↔⊎

-- Functions where the Tree argument should be explicit,
-- * Membership functions have explicit Tree, after Key or K& V.
module _ {v : Level} {V : Value v} {l u : Key⁺} {h : ℕ} where
  _∈_ : (kv : K& V) (t : Tree V l u h) → Set (a ⊔ ℓ₂ ⊔ v)
  _∈_ kv t = Any (kv ≡_) t

  _∈k_ : (k : Key) (t : Tree V l u h) → Set (a ⊔ ℓ₁ ⊔ ℓ₂ ⊔ v)
  _∈k_ k t = Any ((k ≈_) ∘ key) t

  Σ∈ : (t : Tree V l u h) → Set (a ⊔ ℓ₂ ⊔ v)
  Σ∈ t = Σ (K& V) (_∈ t)

-- Functions that implicitly depend on a Tree.
module _ {v : Level} {V : Value v}
         {l u : Key⁺} {h : ℕ} {t : Tree V l u h} where
  lookupKey≈ : {k : Key} (path : k ∈k t) → k ≈ lookupKey path
  lookupKey≈ = lookup-result

  ∈-bounded : {kv : K& V} → kv ∈ t → l < key kv < u
  ∈-bounded path rewrite cong key (lookup-result path) = lookup-bounded path

  ∈k-bounded : {k : Key} → k ∈k t → l < k < u
  ∈k-bounded path = bounds-resp-≈ (Eq.sym (lookupKey≈ path)) (lookup-bounded path)

  lookupKey∈ : {p : Level} {P : Pred (K& V) p}
               (path : Any P t) → lookupKey path ∈k t
  lookupKey∈ path = lookup-rebuild {Q = λ kv → lookupKey path ≈ key kv} path Eq.refl

  lookupKey≉ : {k kp : Key}
    (path : kp ∈k t) → kp ≉ k → lookupKey path ≉ k
  lookupKey≉ path kp≉k kl≈k = contradiction (Eq.trans (lookupKey≈ path) kl≈k) kp≉k

  Any→∈ : {p : Level} {P : Pred (K& V) p}
          (path : Any P t) → Any.lookup path ∈ t
  Any→∈ path = lookup-rebuild path (refl {x = Any.lookup path})

  ∈→Any : {p : Level} {P : Pred (K& V) p} {kv : K& V}
          (kv∈t : kv ∈ t) → P kv → Any P t
  ∈→Any {P = P} {kv = kv} kv∈t Pkv =
    lookup-rebuild {P = _≡_ kv} {Q = P} kv∈t (subst P (lookup-result kv∈t) Pkv)

  Any→Σ∈ : {p : Level} {P : Pred (K& V) p}
           (path : Any P t) → Σ∈ t
  Any→Σ∈ path = Any.lookup path , Any→∈ path

  key-lookup : {k : Key} (k∈t : k ∈k t) → key (Any.lookup k∈t) ≈ k
  key-lookup {k = k} k∈t = Eq.sym (lookup-result {P = (k ≈_) ∘ key} k∈t)

module _ {v : Level} {V : Value v} where
  lookup-rebuild-≡ : {p : Level} {P : Pred (K& V) p} {q : Level} {Q : Pred (K& V) q} →
       ∀ {l u h} {t : Tree V l u h} (p : Any P t) (q : Q (Any.lookup p)) →
       Any.lookup {V = V} {P = Q} (lookup-rebuild p q) ≡ Any.lookup p
  lookup-rebuild-≡ {P = P} {Q = Q} {t = t} p q
    with lookup-rebuild {V = V} {P = P} {Q = Q} {t = t} p q in eq
  lookup-rebuild-≡ (here p) q | here r = refl
  lookup-rebuild-≡ (left p) q | here r with eq
  ... | ()
  lookup-rebuild-≡ (right p) q | here r with eq
  ... | ()
  lookup-rebuild-≡ (here p) q | left r with eq
  ... | ()
  lookup-rebuild-≡ (left p) q | left r with eq
  ... | refl = lookup-rebuild-≡ p q
  lookup-rebuild-≡ (right p) q | left r with eq
  ... | ()
  lookup-rebuild-≡ (here p) q | right r with eq
  ... | ()
  lookup-rebuild-≡ (left p) q | right r with eq
  ... | ()
  lookup-rebuild-≡ (right p) q | right r with eq
  ... | refl = lookup-rebuild-≡ p q

  -- TODO: Is it possible to reduce key-inj to Any→∈-unqiue?
  key-inj : {p : Level} {P : Pred (K& V) p} →
            {q : Level} {Q : Pred (K& V) q} →
            ∀ {l u h} {t : Tree V l u h} (pathP : Any P t) (pathQ : Any Q t) →
            key (Any.lookup pathP) ≈ key (Any.lookup pathQ) → Any.lookup pathP ≡ Any.lookup pathQ
  key-inj {t = node kv lk ku bal} (here pathP) (here pathQ) eq = refl
  key-inj {t = node kv lk ku bal} (here pathP) (left pathQ) eq =
    ⊥-elim (STO.irrefl (Eq.sym eq) ([<]-injective (proj₂ (lookup-bounded pathQ))))
  key-inj {t = node kv lk ku bal} (here pathP) (right pathQ) eq =
    ⊥-elim (STO.irrefl eq ([<]-injective (proj₁ (lookup-bounded pathQ))))
  key-inj {t = node kv lk ku bal} (left pathP) (here pathQ) eq =
    ⊥-elim (STO.irrefl eq ([<]-injective (proj₂ (lookup-bounded pathP))))
  key-inj {t = node kv lk ku bal} (left pathP) (left pathQ) eq = key-inj pathP pathQ eq
  key-inj {t = node kv lk ku bal} (left pathP) (right pathQ) eq =
    ⊥-elim (STO.irrefl eq
                   (STO.trans ([<]-injective (proj₂ (lookup-bounded pathP)))
                            ([<]-injective (proj₁ (lookup-bounded pathQ)))))
  key-inj {t = node kv lk ku bal} (right pathP) (here pathQ) eq =
    ⊥-elim (STO.irrefl (Eq.sym eq) ([<]-injective (proj₁ (lookup-bounded pathP))))
  key-inj {t = node kv lk ku bal} (right pathP) (left pathQ) eq =
    ⊥-elim (STO.irrefl (Eq.sym eq)
                   (STO.trans ([<]-injective (proj₂ (lookup-bounded pathQ)))
                            ([<]-injective (proj₁ (lookup-bounded pathP)))))
  key-inj {t = node kv lk ku bal} (right pathP) (right pathQ) eq = key-inj pathP pathQ eq

-- Functions that implicitly depend on a Tree.
module _ {v : Level} {V : Value v}
         {l u : Key⁺} {h : ℕ} {t : Tree V l u h} where

  Q-path→MaybeAny : {p : Level} {P : Pred (K& V) p} {q : Level} {Q : Pred (K& V) q} →
             {m : Maybe (K& V)} →
             ({kv : K& V} → kv ∈ t → Q kv → m ≡ just kv) →
             (path : Any P t) → Q (Any.lookup path) →
             Maybe.Any P m
  Q-path→MaybeAny {m = m} f path q =
    just→Any m
                      (Any.lookup path)
                      (f (lookup-rebuild path refl) q)
                      (lookup-result path)

  lookup-∈k : {k : Key} (k∈t : k ∈k t) {kv : K& V} (kv∈t : kv ∈ t) →
              k ≈ key kv → Any.lookup k∈t ≡ kv
  lookup-∈k {k = k} k∈t {kv} kv∈t eq =
    trans (key-inj k∈t kv∈t key-eq)
            (sym (lookup-result kv∈t))
    where
    key-eq : key (Any.lookup k∈t) ≈ key (Any.lookup kv∈t)
    key-eq = Eq.trans (Eq.sym (lookup-result k∈t))
                      (subst ((k ≈_) ∘ key) (lookup-result kv∈t) eq)

module _ {v : Level} {V : Value v}
         {l u : Key⁺} {h : ℕ} where
  -- De Morgan conversion of All.node.
  node-¬Any : {p : Level} {P : Pred (K& V) p} →
              ∀ {hˡ hʳ} {kv : K& V} {lk : Tree V l [ key kv ] hˡ} →
              {ku : Tree V [ key kv ] u hʳ} {bal : hˡ ∼ hʳ ⊔ h} →
              ¬ (P kv) → ¬ Any P lk → ¬ Any P ku →
              ¬ Any P (node kv lk ku bal)
  node-¬Any p-kv p-lk p-ku (here x) = p-kv x
  node-¬Any p-kv p-lk p-ku (left p-t) = p-lk p-t
  node-¬Any p-kv p-lk p-ku (right p-t) = p-ku p-t

module _ {v : Level} {V : Value v}
         {l u : Key⁺} {h : ℕ} {t : Tree V l u h} where

  ∈→Any-≡ : {p : Level} {P : Pred (K& V) p} {kv : K& V}
            (kv∈t : kv ∈ t) (Pkv : P kv) →
            kv ≡ Any.lookup {P = P} (∈→Any kv∈t Pkv)
  ∈→Any-≡ {P = P} {kv = kv} kv∈t Pkv =
    trans (lookup-result kv∈t)
            (sym (lookup-rebuild-≡ kv∈t ((subst P (lookup-result kv∈t) Pkv))))

  ∈P→ΣQ : {p : Level} {P : Pred (K& V) p} {q : Level} {Q : Pred (K& V) q} {kv : K& V}
            (kv∈t : kv ∈ t) (Pkv : P kv) (Qkv : Q kv) →
            Σ[ path ∈ Any P t ] Q (Any.lookup path)
  ∈P→ΣQ {P = P} {Q = Q} kv∈t Pkv Qkv =
      ∈→Any kv∈t Pkv
    , subst Q (∈→Any-≡ kv∈t Pkv) Qkv

  MaybeAny→Q-path : {p : Level} {P : Pred (K& V) p} {q : Level} {Q : Pred (K& V) q}
       {m : Maybe (K& V)} →
       ({kv : K& V} → m ≡ just kv → kv ∈ t × Q kv) →
       Maybe.Any P m → Σ[ path ∈ Any P t ] Q (Any.lookup path)
  MaybeAny→Q-path {P = P} {Q = Q} {m = just kv} f (just {x = .kv} Pkv) with f {kv} refl
  ... | (kv∈t , Qkv) = ∈P→ΣQ kv∈t Pkv Qkv

  just-≐→⇔ : {p : Level} {P : Pred (K& V) p} {q : Level} {Q : Pred (K& V) q} →
                {m : Maybe (K& V)} →
                ((λ r → m ≡ just r) ≐ ((_∈ t) ∩ Q)) →
                Maybe.Any P m ⇔ (Σ[ path ∈ Any P t ] Q (Any.lookup path))
  just-≐→⇔ {P = P} {Q = Q} {m = m} eq = mk⇔
    (MaybeAny→Q-path (proj₁ eq))
    (uncurry (Q-path→MaybeAny (curry (proj₂ eq))))

