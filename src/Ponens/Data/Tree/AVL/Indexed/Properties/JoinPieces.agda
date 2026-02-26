{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (StrictTotalOrder)

module Ponens.Data.Tree.AVL.Indexed.Properties.JoinPieces
  {a ℓ₁ ℓ₂} (sto : StrictTotalOrder a ℓ₁ ℓ₂) where

open import Data.Nat using (zero; suc)
open import Data.Product using (_,_; proj₂; ∃)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Level using (Level)
open import Relation.Unary using (Pred)

open import Data.Tree.AVL.Indexed sto using (Tree; Value; K&_; key; Key⁺; [_]; _∼_⊔_; pred[_⊕_]; 0#; 1#; ∼-; ∼0; ∼+; joinʳ⁻; joinˡ⁻)
open import Data.Tree.AVL.Indexed.Relation.Unary.Any sto using (Any; here; left; right)
open import Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties sto using (joinˡ⁺-here⁺; joinˡ⁺-left⁺; joinˡ⁺-right⁺; joinˡ⁺⁻; joinʳ⁺-here⁺; joinʳ⁺-left⁺; joinʳ⁺-right⁺; joinʳ⁺⁻)

module STO = StrictTotalOrder sto
open STO using () renaming (Carrier to Key)

private
  variable
    v p : Level
    V : Value v
    P : Pred (K& V) p

joinʳ⁻-here⁺ : ∀ {l u hˡ hʳ h} →
               (k : K& V) →
               (l : Tree V l [ key k ] hˡ) →
               (r : ∃ λ i → Tree V [ key k ] u pred[ i ⊕ hʳ ]) →
               (bal : hˡ ∼ hʳ ⊔ h) →
               P k →
               Any P (proj₂ (joinʳ⁻ hʳ k l r bal))
joinʳ⁻-here⁺ {hʳ = zero}  k₂ t₁ (0# , t₃) bal path = here path
joinʳ⁻-here⁺ {hʳ = zero}  k₂ t₁ (1# , t₃) bal path = here path
joinʳ⁻-here⁺ {hʳ = suc _} k₂ t₁ (0# , t₃) ∼-  path = joinˡ⁺-here⁺ k₂ (1# , t₁) t₃ ∼- path
joinʳ⁻-here⁺ {hʳ = suc _} k₂ t₁ (0# , t₃) ∼0  path = here path
joinʳ⁻-here⁺ {hʳ = suc _} k₂ t₁ (0# , t₃) ∼+  path = here path
joinʳ⁻-here⁺ {hʳ = suc _} k₂ t₁ (1# , t₃) bal path = here path

joinʳ⁻-left⁺ : ∀ {l u hˡ hʳ h} →
               (k : K& V) →
               (l : Tree V l [ k .key ] hˡ) →
               (r : ∃ λ i → Tree V [ k .key ] u pred[ i ⊕ hʳ ]) →
               (bal : hˡ ∼ hʳ ⊔ h) →
               Any P l → Any P (proj₂ (joinʳ⁻ hʳ k l r bal))
joinʳ⁻-left⁺ {hʳ = zero}  k₂ t₁ (0# , t₃) bal path = left path
joinʳ⁻-left⁺ {hʳ = zero}  k₂ t₁ (1# , t₃) bal path = left path
joinʳ⁻-left⁺ {hʳ = suc _} k₂ t₁ (0# , t₃) ∼-  path = joinˡ⁺-left⁺ k₂ (1# , t₁) t₃ ∼- path
joinʳ⁻-left⁺ {hʳ = suc _} k₂ t₁ (0# , t₃) ∼0  path = left path
joinʳ⁻-left⁺ {hʳ = suc _} k₂ t₁ (0# , t₃) ∼+  path = left path
joinʳ⁻-left⁺ {hʳ = suc _} k₂ t₁ (1# , t₃) bal path = left path

joinʳ⁻-right⁺ : ∀ {l u hˡ hʳ h} →
               (k : K& V) →
               (l : Tree V l [ k .key ] hˡ) →
               (r : ∃ λ i → Tree V [ k .key ] u pred[ i ⊕ hʳ ]) →
               (bal : hˡ ∼ hʳ ⊔ h) →
               Any P (proj₂ r) → Any P (proj₂ (joinʳ⁻ hʳ k l r bal))
joinʳ⁻-right⁺ {hʳ = zero}  k₂ t₁ (0# , t₃) bal path = right path
joinʳ⁻-right⁺ {hʳ = zero}  k₂ t₁ (1# , t₃) bal path = right path
joinʳ⁻-right⁺ {hʳ = suc _} k₂ t₁ (0# , t₃) ∼-  path = joinˡ⁺-right⁺ k₂ (1# , t₁) t₃ ∼- path
joinʳ⁻-right⁺ {hʳ = suc _} k₂ t₁ (0# , t₃) ∼0  path = right path
joinʳ⁻-right⁺ {hʳ = suc _} k₂ t₁ (0# , t₃) ∼+  path = right path
joinʳ⁻-right⁺ {hʳ = suc _} k₂ t₁ (1# , t₃) bal path = right path

joinʳ⁻⁻ : ∀ {l u hˡ hʳ h} →
          (k : K& V) →
          (lk : Tree V l [ k .key ] hˡ) →
          (ku : ∃ λ i → Tree V [ k .key ] u pred[ i ⊕ hʳ ]) →
          (bal : hˡ ∼ hʳ ⊔ h) →
          Any P (proj₂ (joinʳ⁻ hʳ k lk ku bal)) →
          P k ⊎ Any P lk ⊎ Any P (proj₂ ku)
joinʳ⁻⁻ {hʳ = zero}  k₂ t₁ (0# , t₃) bal (here Pk₂) = inj₁ Pk₂
joinʳ⁻⁻ {hʳ = zero}  k₂ t₁ (0# , t₃) bal (left p) = inj₂ (inj₁ p)
joinʳ⁻⁻ {hʳ = zero}  k₂ t₁ (0# , t₃) bal (right p) = inj₂ (inj₂ p)
joinʳ⁻⁻ {hʳ = zero}  k₂ t₁ (1# , t₃) bal (here Pk₂) = inj₁ Pk₂
joinʳ⁻⁻ {hʳ = zero}  k₂ t₁ (1# , t₃) bal (left p) = inj₂ (inj₁ p)
joinʳ⁻⁻ {hʳ = zero}  k₂ t₁ (1# , t₃) bal (right p) = inj₂ (inj₂ p)
joinʳ⁻⁻ {hʳ = suc _} k₂ t₁ (0# , t₃) ∼-  p = joinˡ⁺⁻ k₂ (1# , t₁) t₃ ∼- p
joinʳ⁻⁻ {hʳ = suc _} k₂ t₁ (0# , t₃) ∼0  (here Pk₂) = inj₁ Pk₂
joinʳ⁻⁻ {hʳ = suc _} k₂ t₁ (0# , t₃) ∼0  (left p) = inj₂ (inj₁ p)
joinʳ⁻⁻ {hʳ = suc _} k₂ t₁ (0# , t₃) ∼0  (right p) = inj₂ (inj₂ p)
joinʳ⁻⁻ {hʳ = suc _} k₂ t₁ (0# , t₃) ∼+  (here Pk₂) = inj₁ Pk₂
joinʳ⁻⁻ {hʳ = suc _} k₂ t₁ (0# , t₃) ∼+  (left p) = inj₂ (inj₁ p)
joinʳ⁻⁻ {hʳ = suc _} k₂ t₁ (0# , t₃) ∼+  (right p) = inj₂ (inj₂ p)
joinʳ⁻⁻ {hʳ = suc _} k₂ t₁ (1# , t₃) bal (here Pk₂) = inj₁ Pk₂
joinʳ⁻⁻ {hʳ = suc _} k₂ t₁ (1# , t₃) bal (left p) = inj₂ (inj₁ p)
joinʳ⁻⁻ {hʳ = suc _} k₂ t₁ (1# , t₃) bal (right p) = inj₂ (inj₂ p)

joinˡ⁻-here⁺ : ∀ {l u hˡ hʳ h} →
               (k : K& V) →
               (t₁ : ∃ λ i → Tree V l [ k .key ] pred[ i ⊕ hˡ ]) →
               (t₂ : Tree V [ k .key ] u hʳ) →
               (bal : hˡ ∼ hʳ ⊔ h) →
               P k →
               Any P (proj₂ (joinˡ⁻ hˡ k t₁ t₂ bal))
joinˡ⁻-here⁺ {hˡ = zero}  k₂ (0# , t₁) t₃ bal path = here path
joinˡ⁻-here⁺ {hˡ = zero}  k₂ (1# , t₁) t₃ bal path = here path
joinˡ⁻-here⁺ {hˡ = suc _} k₂ (0# , t₁) t₃ ∼+  path = joinʳ⁺-here⁺ k₂ t₁ (1# , t₃) ∼+ path
joinˡ⁻-here⁺ {hˡ = suc _} k₂ (0# , t₁) t₃ ∼0  path = here path
joinˡ⁻-here⁺ {hˡ = suc _} k₂ (0# , t₁) t₃ ∼-  path = here path
joinˡ⁻-here⁺ {hˡ = suc _} k₂ (1# , t₁) t₃ bal path = here path

joinˡ⁻-left⁺ : ∀ {l u hˡ hʳ h} →
               (k : K& V) →
               (t₁ : ∃ λ i → Tree V l [ k .key ] pred[ i ⊕ hˡ ]) →
               (t₂ : Tree V [ k .key ] u hʳ) →
               (bal : hˡ ∼ hʳ ⊔ h) →
               Any P (proj₂ t₁) →
               Any P (proj₂ (joinˡ⁻ hˡ k t₁ t₂ bal))
joinˡ⁻-left⁺ {hˡ = zero}  k₂ (0# , t₁) t₃ bal path = left path
joinˡ⁻-left⁺ {hˡ = zero}  k₂ (1# , t₁) t₃ bal path = left path
joinˡ⁻-left⁺ {hˡ = suc _} k₂ (0# , t₁) t₃ ∼+  path = joinʳ⁺-left⁺ k₂ t₁ (1# , t₃) ∼+ path
joinˡ⁻-left⁺ {hˡ = suc _} k₂ (0# , t₁) t₃ ∼0  path = left path
joinˡ⁻-left⁺ {hˡ = suc _} k₂ (0# , t₁) t₃ ∼-  path = left path
joinˡ⁻-left⁺ {hˡ = suc _} k₂ (1# , t₁) t₃ bal path = left path

joinˡ⁻-right⁺ : ∀ {l u hˡ hʳ h} →
               (k : K& V) →
               (t₁ : ∃ λ i → Tree V l [ k .key ] pred[ i ⊕ hˡ ]) →
               (t₂ : Tree V [ k .key ] u hʳ) →
               (bal : hˡ ∼ hʳ ⊔ h) →
               Any P t₂ →
               Any P (proj₂ (joinˡ⁻ hˡ k t₁ t₂ bal))
joinˡ⁻-right⁺ {hˡ = zero}  k₂ (0# , t₁) t₃ bal path = right path
joinˡ⁻-right⁺ {hˡ = zero}  k₂ (1# , t₁) t₃ bal path = right path
joinˡ⁻-right⁺ {hˡ = suc _} k₂ (0# , t₁) t₃ ∼+  path = joinʳ⁺-right⁺ k₂ t₁ (1# , t₃) ∼+ path
joinˡ⁻-right⁺ {hˡ = suc _} k₂ (0# , t₁) t₃ ∼0  path = right path
joinˡ⁻-right⁺ {hˡ = suc _} k₂ (0# , t₁) t₃ ∼-  path = right path
joinˡ⁻-right⁺ {hˡ = suc _} k₂ (1# , t₁) t₃ bal path = right path

joinˡ⁻⁻ : ∀ {l u hˡ hʳ h} →
          (k : K& V) →
          (t₁ : ∃ λ i → Tree V l [ k .key ] pred[ i ⊕ hˡ ]) →
          (t₂ : Tree V [ k .key ] u hʳ) →
          (bal : hˡ ∼ hʳ ⊔ h) →
          Any P (proj₂ (joinˡ⁻ hˡ k t₁ t₂ bal)) →
          P k ⊎ Any P (proj₂ t₁) ⊎ Any P t₂
joinˡ⁻⁻ {hˡ = 0#} k₂ (0# , t₁) t₃ bal (here p) = inj₁ p
joinˡ⁻⁻ {hˡ = 0#} k₂ (0# , t₁) t₃ bal (right p) = inj₂ (inj₂ p)
joinˡ⁻⁻ {hˡ = 0#} k₂ (1# , t₁) t₃ bal (here p) = inj₁ p
joinˡ⁻⁻ {hˡ = 0#} k₂ (1# , t₁) t₃ bal (right p) = inj₂ (inj₂ p)
joinˡ⁻⁻ {hˡ = suc _} k₂ (0# , t₁) t₃ ∼+  p = joinʳ⁺⁻ k₂ t₁ (1# , t₃) ∼+ p
joinˡ⁻⁻ {hˡ = suc _} k₂ (0# , t₁) t₃ ∼0 (here p) = inj₁ p
joinˡ⁻⁻ {hˡ = suc _} k₂ (0# , t₁) t₃ ∼0 (left p) = inj₂ (inj₁ p)
joinˡ⁻⁻ {hˡ = suc _} k₂ (0# , t₁) t₃ ∼0 (right p) = inj₂ (inj₂ p)
joinˡ⁻⁻ {hˡ = suc _} k₂ (0# , t₁) t₃ ∼- (here p) = inj₁ p
joinˡ⁻⁻ {hˡ = suc _} k₂ (0# , t₁) t₃ ∼- (left p) = inj₂ (inj₁ p)
joinˡ⁻⁻ {hˡ = suc _} k₂ (0# , t₁) t₃ ∼- (right p) = inj₂ (inj₂ p)
joinˡ⁻⁻ {hˡ = suc _} k₂ (1# , t₁) t₃ bal (here p) = inj₁ p
joinˡ⁻⁻ {hˡ = suc _} k₂ (1# , t₁) t₃ bal (left p) = inj₂ (inj₁ p)
joinˡ⁻⁻ {hˡ = suc _} k₂ (1# , t₁) t₃ bal (right p) = inj₂ (inj₂ p)
