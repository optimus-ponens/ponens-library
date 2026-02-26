{-# OPTIONS --cubical-compatible --safe #-}

module Ponens.Function.Related.TypeIsomorphisms where

open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ; ∃)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Sum.Function.Propositional using (_⊎-↔_)
open import Data.Unit using (⊤; tt)
open import Function using (_∘_; _⇔_; _↔_; Inverse; mk⇔)
open import Function.Properties.Inverse using (↔-refl; ↔-trans)
open import Ponens.Function using (mk↔-∘)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open Inverse using (to; from; inverse)
to∘from : ∀ {ℓA ℓB} {A : Set ℓA} {B : Set ℓB} (eq : A ↔ B) (y : B) → to eq (from eq y) ≡ y
to∘from eq y = proj₁ (inverse eq) refl
from∘to : ∀ {ℓA ℓB} {A : Set ℓA} {B : Set ℓB} (eq : A ↔ B) (x : A) → from eq (to eq x) ≡ x
from∘to eq x = proj₂ (inverse eq) refl

-- De Morgan's Laws
-- TODO: Keep this consistent De Morgan in with Ponens.Data.Tree.AVL.Indexed.Properties.All.
⇔-→-distrib-× : ∀ {ℓA ℓB ℓC} {A : Set ℓA} {B : Set ℓB} {C : Set ℓC} →
              ((A → C) × (B → C)) ⇔ (A ⊎ B → C)
⇔-→-distrib-× {A = A} {B} {C} = mk⇔
  (λ{ (ac , bc) (inj₁ a) → ac a
    ; (ac , bc) (inj₂ b) → bc b })
  (λ h → (h ∘ inj₁) , (h ∘ inj₂))

-- TODO: Also add the version with the _≗_ setoid on the right.
→-distrib-× : ∀ {ℓA ℓB ℓC} {A : Set ℓA} {B : Set ℓB} {C : Set ℓC} →
              (ext : (h1 h2 : (A ⊎ B) → C) → ((x : A ⊎ B) → h1 x ≡ h2 x) → h1 ≡ h2) →
              ((A → C) × (B → C)) ↔ (A ⊎ B → C)
→-distrib-× {A = A} {B} {C} ext = mk↔-∘ f g f∘g g∘f
  where
  f : (A → C) × (B → C) → A ⊎ B → C
  f (ac , bc) (inj₁ a) = ac a
  f (ac , bc) (inj₂ b) = bc b
  g : (A ⊎ B → C) → (A → C) × (B → C)
  g h = (h ∘ inj₁) , (h ∘ inj₂)
  f∘g : (x : (A → C) × (B → C)) → g (f x) ≡ x
  f∘g _ = refl
  g∘f : (h : A ⊎ B → C) → f (g h) ≡ h
  g∘f h = ext (f (g h)) h λ{ (inj₁ _) → refl ; (inj₂ _) → refl}

-- TODO: In cubical this would be (∃ (Q ∪ R) ≡ ∃ Q ⊎ ∃ R) because (P a ≡ Q a ⊎ R a) would be rewritten.
--       So is there a setoid style that reduces this to an algebra on Pred?
Preds↔⊎→∃↔⊎ : ∀ {ℓA ℓP ℓQ ℓR} {A : Set ℓA} {P : A → Set ℓP} {Q : A → Set ℓQ} {R : A → Set ℓR} →
              ((a : A) → P a ↔ (Q a ⊎ R a)) →
              ∃ P ↔ (∃ Q ⊎ ∃ R)
Preds↔⊎→∃↔⊎ {A = A} {P} {Q} {R} eq = mk↔-∘ {A = ∃ P} {B = ∃ Q ⊎ ∃ R} f g f∘g g∘f
  where
  f' : (a : A) → Q a ⊎ R a → ∃ Q ⊎ ∃ R
  f' a (inj₁ r1) = inj₁ (a , r1)
  f' a (inj₂ r2) = inj₂ (a , r2)
  f : ∃ P → ∃ Q ⊎ ∃ R
  f (a , r) = f' a (to (eq a) r)
  g : ∃ Q ⊎ ∃ R → ∃ P
  g (inj₁ (a , r1)) = a , from (eq a) (inj₁ r1)
  g (inj₂ (a , r2)) = a , from (eq a) (inj₂ r2)
  f∘g : (x : ∃ P) → g (f x) ≡ x
  f∘g (a , r) with (to (eq a) r) in eq'
  ... | inj₁ r1 rewrite sym eq' | from∘to (eq a) r = refl
  ... | inj₂ r2 rewrite sym eq' | from∘to (eq a) r = refl
  g∘f : (y : ∃ Q ⊎ ∃ R) → f (g y) ≡ y
  g∘f (inj₁ (a , r1)) rewrite to∘from (eq a) (inj₁ r1) = refl
  g∘f (inj₂ (a , r2)) rewrite to∘from (eq a) (inj₂ r2) = refl

Preds↔⊎3→∃↔⊎3 : ∀ {ℓA ℓP ℓQ ℓR ℓS} {A : Set ℓA} →
                {P : A → Set ℓP} {Q : A → Set ℓQ} {R : A → Set ℓR} {S : A → Set ℓS} →
                ((a : A) → P a ↔ (Q a ⊎ R a ⊎ S a)) →
                ∃ P ↔ (∃ Q ⊎ ∃ R ⊎ ∃ S)
Preds↔⊎3→∃↔⊎3 {A = A} {P} {Q} {R} {S} eq =
   ↔-trans (Preds↔⊎→∃↔⊎ eq)
           (↔-refl ⊎-↔ Preds↔⊎→∃↔⊎ λ a → ↔-refl)

Σ≡↔⊤ : ∀ {ℓA} {A : Set ℓA} (x : A) → (Σ A (_≡ x)) ↔ ⊤
Σ≡↔⊤ {A = A} x = mk↔-∘
  (λ{ (x' , refl) → tt})
  (λ{ tt → x , refl})
  (λ{ (x' , refl) → refl})
  (λ{ tt → refl})
