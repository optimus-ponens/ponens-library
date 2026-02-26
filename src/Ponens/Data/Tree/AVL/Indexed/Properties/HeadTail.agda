{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (StrictTotalOrder)

module Ponens.Data.Tree.AVL.Indexed.Properties.HeadTail
  {a ℓ₁ ℓ₂} (sto : StrictTotalOrder a ℓ₁ ℓ₂) where

open import Data.Maybe using (nothing; just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (zero; suc; _+_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)
open import Relation.Unary using (Pred)

open import Data.Tree.AVL.Indexed sto using (Tree; leaf; node; Value; K&_; key; _,_; Key⁺; [_]; _<⁺_; ℕ₂; _⊕_; ∼+; ∼0; ∼-; headTail; initLast)
open import Data.Tree.AVL.Indexed.Relation.Unary.Any sto as Any using (Any; here; left; right)
open import Data.Tree.AVL.Indexed.Relation.Unary.All sto as All using (All)
open import Ponens.Data.Tree.AVL.Indexed sto using (head)
open import Ponens.Data.Tree.AVL.Indexed.Properties.All sto using (Any×All-∈; All-Any; All¬⇒¬Any)
open import Ponens.Data.Tree.AVL.Indexed.Properties.Any sto using (_∈_)
open import Ponens.Data.Tree.AVL.Indexed.Properties.Gap sto using (_>-∈_; _<-∈_)
open import Ponens.Data.Tree.AVL.Indexed.Properties.JoinPieces sto using (joinˡ⁻⁻; joinˡ⁻-here⁺; joinˡ⁻-left⁺; joinˡ⁻-right⁺; joinʳ⁻⁻; joinʳ⁻-here⁺; joinʳ⁻-right⁺; joinʳ⁻-left⁺)
open import Ponens.Data.Tree.AVL.Indexed.Properties.Range sto using (All-bounded)

module STO = StrictTotalOrder sto
open STO using (module Eq; _<_) renaming (Carrier to Key)
open import Relation.Binary.Construct.Add.Extrema.Strict _<_ using ([<]-injective)

private
  variable
    v p : Level
    V : Value v
    P : Pred (K& V) p

headTail-head⁻ : ∀ {l u h} → (t : Tree V l u (suc h)) → P (proj₁ (headTail t)) →
                 Any P t
headTail-head⁻ (node k₁ (leaf l<k₁) t₂ ∼+) path = here path
headTail-head⁻ (node k₁ (leaf l<k₁) t₂ ∼0) path = here path
headTail-head⁻ (node {hˡ = suc _} k₃ t₁₂ t₄ bal) path with headTail t₁₂
headTail-head⁻ (node {hˡ = suc _} k₃ t₁₂@(node _ _ _ _) t₄ bal) path | k₁ , l<k₁ , t₂
  = left (headTail-head⁻ t₁₂ path)

headTail-tail⁻ : ∀ {l u h} → (t : Tree V l u (1 + h)) → Any P (proj₂ (proj₂ (proj₂ (headTail t)))) →
                 Any P t
headTail-tail⁻ (node k₁ (leaf l<k₁) t₂ ∼+) p = right p
headTail-tail⁻ (node k₁ (leaf l<k₁) t₂ ∼0) p = right p
headTail-tail⁻ (node {hˡ = suc _} k₃ t₁₂@(node _ _ _ _) t₄ bal) p
  with k₁ , l<k₁ , t₂ ← headTail t₁₂ in eq
     | joinˡ⁻⁻ k₃ t₂ t₄ bal p
     | bal -- Match on `bal` for the termination checker to see `h` decreases.
     | eq
... | inj₁ Pk₃ | _ | refl = here Pk₃
... | inj₂ (inj₁ p₂) | ∼+ | refl = left (headTail-tail⁻ t₁₂ p₂)
... | inj₂ (inj₁ p₂) | ∼0 | refl = left (headTail-tail⁻ t₁₂ p₂)
... | inj₂ (inj₁ p₂) | ∼- | refl = left (headTail-tail⁻ t₁₂ p₂)
... | inj₂ (inj₂ p₄) | _ | refl = right p₄

headTail⁺ : ∀ {l u h} → (t : Tree V l u (1 + h)) →
            Any P t → P (proj₁ (headTail t)) ⊎ Any P (proj₂ (proj₂ (proj₂ (headTail t))))
headTail⁺ (node k₁ (leaf l<k₁) t₂ ∼+) (here path) = inj₁ path
headTail⁺ (node k₁ (leaf l<k₁) t₂ ∼+) (right path) = inj₂ path
headTail⁺ (node k₁ (leaf l<k₁) t₂ ∼0) (here path) = inj₁ path
headTail⁺ (node {hˡ = suc _} k₃ t₁₂@(node _ _ _ _) t₄ bal) (here path) with headTail t₁₂
... | k₁ , l<k₁ , t₂ = inj₂ (joinˡ⁻-here⁺ k₃ t₂ t₄ bal path)
headTail⁺ (node {hˡ = suc _} k₃ t₁₂@(node _ _ _ _) t₄ bal) (left path) with headTail t₁₂ | headTail⁺ t₁₂ path
... | k₁ , l<k₁ , t₂ | inj₁ path' = inj₁ path'
... | k₁ , l<k₁ , t₂ | inj₂ path' = inj₂ (joinˡ⁻-left⁺ k₃ t₂ t₄ bal path')
headTail⁺ (node {hˡ = suc _} k₃ t₁₂@(node _ _ _ _) t₄ bal) (right path) with headTail t₁₂
... | k₁ , l<k₁ , t₂ = inj₂ (joinˡ⁻-right⁺ k₃ t₂ t₄ bal path)

headTail-All⁻ : ∀ {l u h} → (t : Tree V l u (1 + h)) →
                P (proj₁ (headTail t)) → All P (proj₂ (proj₂ (proj₂ (headTail t)))) →
                All P t
headTail-All⁻ {V = V} {P = P} t P-head P-tail =
  All.map path→P (All-Any t)
  where
  path→P : {kv : K& V} → Any (kv ≡_) t → P kv
  path→P {kv} kv∈t with headTail⁺ {P = kv ≡_} t kv∈t
  ... | inj₁ refl = P-head
  ... | inj₂ kv∈tail = Any×All-∈ kv∈tail P-tail

headTail→¬Any< : ∀ {l u h} (t : Tree V l u (suc h)) →
     (k : K& V) (l<k : l <⁺ [ key k ]) (i : ℕ₂) (tail : Tree V [ key k ] u (i ⊕ h)) →
     (headTail t ≡ (k , l<k , i , tail)) →
     ¬ (key k >-∈ t)
headTail→¬Any< t (k , _) l<k i tail refl = All¬⇒¬Any
  (headTail-All⁻ t (STO.irrefl Eq.refl)
    (All.map (λ {kv} (k<kv , _) → STO.asym ([<]-injective k<kv)) (All-bounded tail)))

head-cases : ∀ {l u h} (t : Tree V l u h) →
         (  head {V = V} t ≡ nothing
          × ((k : Key) → ¬ (k <-∈ t)))
        ⊎ ∃ λ r → head {V = V} t ≡ just r
                × (r ∈ t)
                × ¬ ((key r) >-∈ t)
head-cases {h = zero} (leaf l<u) = inj₁ (refl , λ{ _ ()})
head-cases {V = V} {l = l} {u} {h = suc h} t@(node {hˡ = ĥˡ} (k , _) lk ku bal)
  with headTail t in eq
     | headTail-head⁻ {P = (head t ≡_) ∘ just} t refl
... | (hk , hv) , l<k , i , tail | p =
  inj₂ ((hk , hv)
       , refl
       , Any.map just-injective p
       , headTail→¬Any< t (hk , hv) l<k i tail eq)

initLast-last⁻ : ∀ {l u h} → (t : Tree V l u (suc h)) → P (proj₁ (initLast t)) →
                 Any P t
initLast-last⁻ (node k₂ t₁ (leaf k₂<u) ∼-) path = here path
initLast-last⁻ (node k₂ t₁ (leaf k₂<u) ∼0) path = here path
initLast-last⁻ (node {hʳ = suc _} k₂ t₁ t₃₄ bal) path with initLast t₃₄
initLast-last⁻ (node {hʳ = suc _} k₂ t₁ t₃₄@(node _ _ _ _) bal) path | k₄ , k₄<u , t₃
  = right (initLast-last⁻ t₃₄ path)

initLast-init⁻ : ∀ {l u h} → (t : Tree V l u (1 + h)) → Any P (proj₂ (proj₂ (proj₂ (initLast t)))) →
                 Any P t
initLast-init⁻ (node k₂ t₁ (leaf k₂<u) ∼-) p = left p
initLast-init⁻ (node k₂ t₁ (leaf k₂<u) ∼0) p = left p
initLast-init⁻ (node {hʳ = suc _} k₂ t₁ t₃₄@(node _ _ _ _) bal) p
  with k₄ , k₄<u , t₃ ← initLast t₃₄ in eq
     | joinʳ⁻⁻ k₂ t₁ t₃ bal p
     | bal -- Match on `bal` for the termination checker to see `h` decreases.
     | eq
... | inj₁ Pk₃ | _ | refl = here Pk₃
... | inj₂ (inj₂ p₂) | ∼+ | refl = right (initLast-init⁻ t₃₄ p₂)
... | inj₂ (inj₂ p₂) | ∼0 | refl = right (initLast-init⁻ t₃₄ p₂)
... | inj₂ (inj₂ p₂) | ∼- | refl = right (initLast-init⁻ t₃₄ p₂)
... | inj₂ (inj₁ p₄) | _ | refl = left p₄

initLast⁺ : ∀ {l u h} → (t : Tree V l u (1 + h)) →
            Any P t → P (proj₁ (initLast t)) ⊎ Any P (proj₂ (proj₂ (proj₂ (initLast t))))
initLast⁺ (node k₂ t₁ (leaf k₂<u) ∼-) (here path) = inj₁ path
initLast⁺ (node k₂ t₁ (leaf k₂<u) ∼-) (left path) = inj₂ path
initLast⁺ (node k₂ t₁ (leaf k₂<u) ∼0) (here path) = inj₁ path
initLast⁺ (node {hʳ = suc _} k₂ t₁ t₃₄@(node _ _ _ _) bal) (here path) with initLast t₃₄
... | k₄ , k₄<u , t₃ = inj₂ (joinʳ⁻-here⁺ k₂ t₁ t₃ bal path)
initLast⁺ (node {hʳ = suc _} k₂ t₁ t₃₄@(node _ _ _ _) bal) (right path) with initLast t₃₄ | initLast⁺ t₃₄ path
... | k₄ , k₄<u , t₃ | inj₁ path' = inj₁ path'
... | k₄ , k₄<u , t₃ | inj₂ path' = inj₂ (joinʳ⁻-right⁺ k₂ t₁ t₃ bal path')
initLast⁺ (node {hʳ = suc _} k₂ t₁ t₃₄@(node _ _ _ _) bal) (left path) with initLast t₃₄
... | k₄ , k₄<u , t₃ = inj₂ (joinʳ⁻-left⁺ k₂ t₁ t₃ bal path)
