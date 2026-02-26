{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (StrictTotalOrder)

module Ponens.Data.Tree.AVL.Indexed.Properties.Join
  {a ℓ₁ ℓ₂} (sto : StrictTotalOrder a ℓ₁ ℓ₂) where

open import Data.Nat using (suc)
open import Data.Product using (_,_; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Unary using (Pred)

open import Data.Tree.AVL.Indexed sto using (Tree; leaf; node; Value; K&_; _,_; Key⁺; [_]; _∼_⊔_; ∼-; join; headTail; castʳ)
open import Data.Tree.AVL.Indexed.Relation.Unary.Any sto using (Any; left; right)
open import Ponens.Data.Tree.AVL.Indexed.Properties.Cast sto using (castʳ⁺; castʳ⁻)
open import Ponens.Data.Tree.AVL.Indexed.Properties.HeadTail sto using (headTail⁺; headTail-head⁻; headTail-tail⁻)
open import Ponens.Data.Tree.AVL.Indexed.Properties.JoinPieces sto using (joinʳ⁻-left⁺; joinʳ⁻-here⁺; joinʳ⁻-right⁺; joinʳ⁻⁻)

module STO = StrictTotalOrder sto
open STO using () renaming (Carrier to Key)

module _ {v : Level} {V : Value v}
         {p : Level} {P : Pred (K& V) p} where
  private
    Val  = Value.family V
    Val≈ = Value.respects V

  join-left⁺ : ∀ {l m u hˡ hʳ h} →
              (t₁ : Tree V l m hˡ) → (t₂ : Tree V m u hʳ) → (bal : hˡ ∼ hʳ ⊔ h) →
              Any P t₁ → Any P (proj₂ (join t₁ t₂ bal))
  join-left⁺ t₁ (leaf m<u) ∼- path = castʳ⁺ path
  join-left⁺ {hʳ = suc _} t₁ t₂₃@(node _ _ _ _) bal path with headTail t₂₃
  ... | (k₂ , m<k₂ , t₃) = joinʳ⁻-left⁺ k₂ (castʳ t₁ m<k₂) t₃ bal (castʳ⁺ path)

  join-right⁺ : ∀ {l m u hˡ hʳ h} →
              (t₁ : Tree V l m hˡ) → (t₂ : Tree V m u hʳ) → (bal : hˡ ∼ hʳ ⊔ h) →
              Any P t₂ → Any P (proj₂ (join t₁ t₂ bal))
  join-right⁺ t₁ (leaf m<u) ∼- ()
  join-right⁺ {hʳ = suc _} t₁ t₂₃@(node _ _ _ _) bal path with headTail t₂₃ | headTail⁺ t₂₃ path
  ... | k₂ , m<k₂ , t₃ | inj₁ path' = joinʳ⁻-here⁺ k₂ (castʳ t₁ m<k₂) t₃ bal path'
  ... | k₂ , m<k₂ , t₃ | inj₂ path' = joinʳ⁻-right⁺ k₂ (castʳ t₁ m<k₂) t₃ bal path'

  join⁻ : ∀ {l m u hˡ hʳ h} →
           (t₁ : Tree V l m hˡ) → (t₂ : Tree V m u hʳ) → (bal : hˡ ∼ hʳ ⊔ h) →
           Any P (proj₂ (join t₁ t₂ bal)) →
           Any P t₁ ⊎ Any P t₂
  join⁻ t₁ (leaf m<u) ∼- p = inj₁ (castʳ⁻ p)
  join⁻ {hʳ = suc _} t₁ t₂₃@(node _ _ _ _) bal p
    with (k₂ , m<k₂ , t₃) ← headTail t₂₃ in eq
       | joinʳ⁻⁻ k₂ (castʳ t₁ m<k₂) t₃ bal p
       | eq
  ... | inj₁ p | refl = inj₂ (headTail-head⁻ t₂₃ p)
  ... | inj₂ (inj₁ p) | refl = inj₁ (castʳ⁻ p)
  ... | inj₂ (inj₂ p) | refl = inj₂ (headTail-tail⁻ t₂₃ p)

  join-node⁻ : ∀ {l u hˡ hʳ h} {k′ : Key} (v : Val k′) (lp : Tree V l [ k′ ] hˡ) →
          (pu : Tree V [ k′ ] u hʳ) →
          (bal : hˡ ∼ hʳ ⊔ h) →
          Any P (proj₂ (join lp pu bal)) →
          Any P (node (k′ , v) lp pu bal)
  join-node⁻ v lp pu bal path with join⁻ lp pu bal path
  ... | inj₁ path = left path
  ... | inj₂ path = right path
