{-# OPTIONS --cubical-compatible --safe #-}

module Ponens.Relation.Unary.Properties where

open import Data.Empty using (⊥; ⊥-elim)
import Data.Empty.Polymorphic as Poly
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product as × using (_×_; _,_; <_,_>; proj₁; proj₂; ∃)
open import Data.Sum as ⊎ using (_⊎_; [_,_]; inj₁; inj₂)
open import Data.Unit using (tt)
open import Function using (const; id; _∘_; _⇔_; _↔_; Equivalence; mk⇔)
open import Function.Properties.Inverse using (Inverse⇒Equivalence)
open import Level using (Level; _⊔_)
open import Ponens.Relation.Nullary.Properties using (Dec-elim)
open import Relation.Binary using (REL)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Unary using (Pred; _≐_; _⊆_; _⊆′_; _∪_; _∩_; _∖_; _⇒_; ∁; U; ∅; Decidable; Universal; Empty; Satisfiable)
open import Relation.Unary.Algebra using (∩-cong; ∪-cong)
open import Relation.Unary.Properties using (≐-refl)

private
  variable
    a b c p q ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
    A : Set a
    B : Set b
    C : Set c

⇔→≐ : {P : Pred A p} {Q : Pred A q} → ((x : A) → P x ⇔ Q x) → P ≐ Q
⇔→≐ eq = (λ {x = x} Px → eq x .Equivalence.to Px)
       , (λ {x = x} Qx → eq x .Equivalence.from Qx)

↔→≐ : {P : Pred A p} {Q : Pred A q} → ((x : A) → P x ↔ Q x) → P ≐ Q
↔→≐ eq = ⇔→≐ (Inverse⇒Equivalence ∘ eq)

≐→⇔ : {P : Pred A p} {Q : Pred A q} {R : Pred A ℓ₃} → P ≐ Q → (P ⊆ R) ⇔ (Q ⊆ R)
≐→⇔ (PQ , QP) = mk⇔ (λ ∁P {_} Qx → ∁P (QP Qx)) λ ∁Q {_} Px → ∁Q (PQ Px)
≐→⇔′ : {P : Pred A p} {Q : Pred A q} {R : Pred A ℓ₃} → P ≐ Q → (P ⊆′ R) ⇔ (Q ⊆′ R)
≐→⇔′ (PQ , QP) = mk⇔ (λ ∁P x Qx → ∁P x (QP Qx)) λ ∁Q x Px → ∁Q x (PQ Px)

-- TODO: Should this be a Respects law? (_⇒ R) respects _≐_
≐-⇒ : {P : Pred A p} {Q : Pred A q} {R : Pred A ℓ₃} → P ≐ Q → P ⇒ R ≐ Q ⇒ R
≐-⇒ (p→q , q→p) = (λ p→r → p→r ∘ q→p) , (λ q→r → q→r ∘ p→q)

≐-on : {P : Pred B ℓ₁} {Q : Pred B ℓ₂} (f : A → B) → P ≐ Q → P ∘ f ≐ Q ∘ f
≐-on f (pq , qp) = (λ {_} → pq) , (λ {_} → qp)

-- De Morgan's laws

R-∪⊆∩-R : (P : Pred A p) (Q : Pred A q) (R : Pred A ℓ₃) → (P ∪ Q) ⇒ R ⊆ (P ⇒ R) ∩ (Q ⇒ R)
R-∪⊆∩-R _ _ _ f = (λ p → f (inj₁ p)) , (λ q → f (inj₂ q))

∩-R⊆R-∪ : (P : Pred A p) (Q : Pred A q) (R : Pred A ℓ₃) → (P ⇒ R) ∩ (Q ⇒ R) ⊆ (P ∪ Q) ⇒ R
∩-R⊆R-∪ _ _ _ (¬p , _) (inj₁ p) = ¬p p
∩-R⊆R-∪ _ _ _ (_ , ¬q) (inj₂ q) = ¬q q

R-∪≐∩-R : (P : Pred A p) (Q : Pred A q) (R : Pred A ℓ₃) → (P ∪ Q) ⇒ R ≐ (P ⇒ R) ∩ (Q ⇒ R)
R-∪≐∩-R P Q R = R-∪⊆∩-R P Q R , ∩-R⊆R-∪ P Q R

∁-∪⊆∩-∁ : (P : Pred A p) (Q : Pred A q) → ∁ (P ∪ Q) ⊆ ∁ P ∩ ∁ Q
∁-∪⊆∩-∁ P Q = R-∪⊆∩-R P Q ∅

∩-∁⊆∁-∪ : (P : Pred A p) (Q : Pred A q) → ∁ P ∩ ∁ Q ⊆ ∁ (P ∪ Q)
∩-∁⊆∁-∪ P Q = ∩-R⊆R-∪ P Q ∅

∁-∪≐∩-∁ : (P : Pred A p) (Q : Pred A q) → ∁ (P ∪ Q) ≐ ∁ P ∩ ∁ Q
∁-∪≐∩-∁ P Q = R-∪≐∩-R P Q ∅

≐-∁ : {P : Pred A p} {Q : Pred A q} → P ≐ Q → ∁ P ≐ ∁ Q
≐-∁ = ≐-⇒ {R = ∅}

∖-cong : {P1 : Pred A ℓ₁} {P2 : Pred A ℓ₂} {Q1 : Pred A ℓ₃} {Q2 : Pred A ℓ₄} →
         (P1 ≐ P2) → (Q1 ≐ Q2) → (P1 ∖ Q1) ≐ (P2 ∖ Q2)
∖-cong Peq Qeq =
    (λ pq → proj₁ Peq (proj₁ pq) , proj₂ pq ∘ proj₂ Qeq)
  , (λ pq → proj₂ Peq (proj₁ pq) , proj₂ pq ∘ proj₁ Qeq)

∩-congˡ : {ℓ : Level} {P1 : Pred A ℓ} {P2 : Pred A ℓ} {Q : Pred A ℓ} →
          P1 ≐ P2 → (P1 ∩ Q) ≐ (P2 ∩ Q)
∩-congˡ eq = ∩-cong eq ≐-refl
∩-congʳ : {ℓ : Level} {P : Pred A ℓ} {Q1 : Pred A ℓ} {Q2 : Pred A ℓ} →
          Q1 ≐ Q2 → (P ∩ Q1) ≐ (P ∩ Q2)
∩-congʳ eq = ∩-cong ≐-refl eq
∪-congˡ : {ℓ : Level} {P1 : Pred A ℓ} {P2 : Pred A ℓ} {Q : Pred A ℓ} →
            P1 ≐ P2 → (P1 ∪ Q) ≐ (P2 ∪ Q)
∪-congˡ eq = ∪-cong eq ≐-refl
∪-congʳ : {ℓ : Level} {P : Pred A ℓ} {Q1 : Pred A ℓ} {Q2 : Pred A ℓ} →
            Q1 ≐ Q2 → (P ∪ Q1) ≐ (P ∪ Q2)
∪-congʳ eq = ∪-cong ≐-refl eq
∩-idemˡ : (P : Pred A p) (Q : Pred A ℓ₁) → P ∩ (P ∩ Q) ≐ P ∩ Q
∩-idemˡ P Q = (λ{ {_} (_ , pq) → pq}) , (λ{ {_} (p , q) → p , p , q})
∪-idemˡ : (P : Pred A p) (Q : Pred A ℓ₁) → P ∪ (P ∪ Q) ≐ P ∪ Q
∪-idemˡ P Q = (λ{ {x} (inj₁ p) → inj₁ p ; {x} (inj₂ pq) → pq})
             , (λ{ {x} pq → inj₂ pq})


-- Properties similar to those in Relation.Unary.Algebra:
-- The difference is these allow Preds on different universes.
-- Further, ∅ and U are not universe-polymorphic.
-- Because the Preds can be on different levels there's no motivation to
-- make ∅ or U to be on the same level as the other Pred.

ℓ-∩-cong : {P1 : Pred A ℓ₁} {P2 : Pred A ℓ₂} {Q1 : Pred A ℓ₃} {Q2 : Pred A ℓ₄} →
           P1 ≐ P2 → Q1 ≐ Q2 → (P1 ∩ Q1) ≐ (P2 ∩ Q2)
ℓ-∩-cong (P⊆Q , Q⊆P) (R⊆S , S⊆R) = ×.map P⊆Q R⊆S , ×.map Q⊆P S⊆R

ℓ-∩-congˡ : {P1 : Pred A ℓ₁} {P2 : Pred A ℓ₂} {Q : Pred A ℓ₃} →
            P1 ≐ P2 → (P1 ∩ Q) ≐ (P2 ∩ Q)
ℓ-∩-congˡ eq = ℓ-∩-cong eq ≐-refl

ℓ-∩-congʳ : {P : Pred A p} {Q1 : Pred A ℓ₂} {Q2 : Pred A ℓ₃} →
            Q1 ≐ Q2 → (P ∩ Q1) ≐ (P ∩ Q2)
ℓ-∩-congʳ eq = ℓ-∩-cong ≐-refl eq

ℓ-∩-comm : (P : Pred A p) (Q : Pred A q) → P ∩ Q ≐ Q ∩ P
ℓ-∩-comm _ _ = ×.swap , ×.swap

ℓ-∩-assoc : (P : Pred A p) (Q : Pred A q) (R : Pred A ℓ₄) → (P ∩ Q) ∩ R ≐ P ∩ (Q ∩ R)
ℓ-∩-assoc _ _ _ = ×.assocʳ′ , ×.assocˡ′

ℓ-∩-idem : (P : Pred A p) → P ∩ P ≐ P
ℓ-∩-idem _ = proj₁ , < id , id >

ℓ-∩-identityˡ : (P : Pred A p) → (U ∩ P) ≐ P
ℓ-∩-identityˡ _ = proj₂ , < const tt , id >

ℓ-∩-identityʳ : (P : Pred A p) → (P ∩ U) ≐ P
ℓ-∩-identityʳ _ = proj₁ , < id , const tt >

ℓ-∩-zeroˡ : (P : Pred A p) → ∅ ∩ P ≐ ∅
ℓ-∩-zeroˡ _ = proj₁ , ⊥-elim

ℓ-∩-zeroʳ : (P : Pred A p) → P ∩ ∅ ≐ ∅
ℓ-∩-zeroʳ _ = proj₂ , ⊥-elim

ℓ-∪-cong : {P1 : Pred A ℓ₁} {P2 : Pred A ℓ₂} {Q1 : Pred A ℓ₃} {Q2 : Pred A ℓ₄} →
           P1 ≐ P2 → Q1 ≐ Q2 → (P1 ∪ Q1) ≐ (P2 ∪ Q2)
ℓ-∪-cong (P⊆Q , Q⊆P) (R⊆S , S⊆R) = ⊎.map P⊆Q R⊆S , ⊎.map Q⊆P S⊆R

ℓ-∪-congˡ : {P1 : Pred A ℓ₁} {P2 : Pred A ℓ₂} {Q : Pred A ℓ₃} →
            P1 ≐ P2 → (P1 ∪ Q) ≐ (P2 ∪ Q)
ℓ-∪-congˡ eq = ℓ-∪-cong eq ≐-refl

ℓ-∪-congʳ : {P : Pred A p} {Q1 : Pred A ℓ₂} {Q2 : Pred A ℓ₃} →
            Q1 ≐ Q2 → (P ∪ Q1) ≐ (P ∪ Q2)
ℓ-∪-congʳ eq = ℓ-∪-cong ≐-refl eq

ℓ-∪-comm : (P : Pred A p) (Q : Pred A q) → P ∪ Q ≐ Q ∪ P
ℓ-∪-comm _ _ = ⊎.swap , ⊎.swap

ℓ-∪-assoc : (P : Pred A p) (Q : Pred A q) (R : Pred A ℓ₄) → (P ∪ Q) ∪ R ≐ P ∪ (Q ∪ R)
ℓ-∪-assoc _ _ _ = ⊎.assocʳ , ⊎.assocˡ

ℓ-∪-idem : (P : Pred A p) → P ∪ P ≐ P
ℓ-∪-idem _ = [ id , id ] , inj₁

ℓ-∪-identityˡ : (P : Pred A p) → (∅ ∪ P) ≐ P
ℓ-∪-identityˡ _ = [ ⊥-elim , id ] , inj₂

ℓ-∪-identityʳ : (P : Pred A p) → (P ∪ ∅) ≐ P
ℓ-∪-identityʳ _ = [ id , ⊥-elim ] , inj₁

ℓ-∩-idemˡ : (P : Pred A p) (Q : Pred A q) → P ∩ (P ∩ Q) ≐ P ∩ Q
ℓ-∩-idemˡ P Q = (λ{ {_} (_ , pq) → pq}) , (λ{ {_} (p , q) → p , p , q})

ℓ-∪-idemˡ : (P : Pred A p) (Q : Pred A q) → P ∪ (P ∪ Q) ≐ P ∪ Q
ℓ-∪-idemˡ P Q = (λ{ {x} (inj₁ p) → inj₁ p ; {x} (inj₂ pq) → pq})
             , (λ{ {x} pq → inj₂ pq})

Decidable→∁ : {P : Pred A p} → Decidable P → Π[ P ∪ ∁ P ]
Decidable→∁ {P = P} P? x = Dec-elim inj₁ inj₂ (P? x)
∁→Decidable : {P : Pred A p} → Π[ P ∪ ∁ P ] → Decidable P
∁→Decidable dec x with dec x
... | inj₁ p = yes p
... | inj₂ ¬p = no ¬p
Decidable⇔∁ : (P : Pred A p) → Decidable P ⇔ Π[ P ∪ ∁ P ]
Decidable⇔∁ _ = mk⇔ Decidable→∁ ∁→Decidable

P∪[Q∩R]⊆P∪R : (P : Pred A p) (Q : Pred A q) (R : Pred A ℓ₃) → P ∪ (Q ∩ R) ⊆ P ∪ R
P∪[Q∩R]⊆P∪R _ _ _ = λ{ (inj₁ p) → inj₁ p ; (inj₂ (_ , q)) → inj₂ q}
P∪R⊆P∪[Q∩R] : {P : Pred A p} {Q : Pred A q} → Π[ P ∪ Q ] → (R : Pred A ℓ₃) → P ∪ R ⊆ P ∪ (Q ∩ R)
P∪R⊆P∪[Q∩R] dec _ {x} pr with dec x | pr
... | inj₁ p | _ = inj₁ p
... | inj₂ q | inj₁ p = inj₁ p
... | inj₂ q | inj₂ r = inj₂ (q , r)
P∪[Q∩R]≐P∪R : {P : Pred A p} {Q : Pred A q} → Π[ P ∪ Q ] → (R : Pred A ℓ₃) → P ∪ (Q ∩ R) ≐ P ∪ R
P∪[Q∩R]≐P∪R {P = P} {Q} dec R = P∪[Q∩R]⊆P∪R P Q R , P∪R⊆P∪[Q∩R] dec R

Empty-∩∁ : (P : Pred A p) → Empty (P ∩ ∁ P)
Empty-∩∁ _ _ (p , ¬p) = ¬p p
Empty-∁∩ : (P : Pred A p) → Empty (∁ P ∩ P)
Empty-∁∩ _ _ (¬p , p) = ¬p p

P∩[Q∪R]⊆P∩R : {P : Pred A p} {Q : Pred A q} → Empty (P ∩ Q) → (R : Pred A ℓ₃) → P ∩ (Q ∪ R) ⊆ P ∩ R
P∩[Q∪R]⊆P∩R nil _ {x} (p , inj₁ q) with nil x
... | ¬pq = ⊥-elim (¬pq (p , q))
P∩[Q∪R]⊆P∩R _ _ (p , inj₂ r) = p , r
P∩R⊆P∩[Q∪R] : (P : Pred A p) → (Q : Pred A q) → (R : Pred A ℓ₃) → P ∩ R ⊆ P ∩ (Q ∪ R)
P∩R⊆P∩[Q∪R] _ _ _ (p , q) = p , inj₂ q
P∩[Q∪R]≐P∩R : {P : Pred A p} {Q : Pred A q} → Empty (P ∩ Q) → (R : Pred A ℓ₃) → P ∩ (Q ∪ R) ≐ P ∩ R
P∩[Q∪R]≐P∩R {P = P} {Q} nil R = P∩[Q∪R]⊆P∩R nil R , P∩R⊆P∩[Q∪R] P Q R

Universal→≐ : {P : Pred A p} {Q : Pred A q} → Universal P → Universal Q → P ≐ Q
Universal→≐ p q = (λ {x} _ → q x) , (λ {x} _ → p x)

≐→Satisfiable⇔ : {P : Pred A p} {Q : Pred A q} → P ≐ Q → Satisfiable P ⇔ Satisfiable Q
≐→Satisfiable⇔ (PQ , QP) =
  mk⇔ (λ{ (x , Px) → x , PQ Px})
      (λ{ (y , Qy) → y , QP Qy})

≐→Empty⇔ : {P : Pred A p} {Q : Pred A q} → P ≐ Q → Empty P ⇔ Empty Q
≐→Empty⇔ eq = ≐→⇔′ {R = λ _ → ⊥} eq

Empty-∩ˡ : {P : Pred A p} {Q : Pred A q} → Empty P → Empty (P ∩ Q)
Empty-∩ˡ e = λ x (p , q) → e x p

Empty-∖ˡ : {P : Pred A p} {Q : Pred A q} → Empty P → Empty (P ∖ Q)
Empty-∖ˡ = Empty-∩ˡ

-- TODO: The stdlib sometimes uses a more general decide than Decidable.
--   e.g. Data/Tree/AVL/Indexed/Relation/Unary/All.agda has
--        decide : Π[ P ∪ Q ] → (t : Tree V l u n) → All P t ⊎ Any Q t

Empty-∖→⊆ : (P : Pred A p) → {Q : Pred A q} → Decidable Q → Empty (P ∖ Q) → P ⊆ Q
Empty-∖→⊆ P Q? e {x} p =
  Dec-elim id
           (λ ¬q → ⊥-elim (e x (p , ¬q)))
           (Q? x)
⊆→Empty-∖ : (P : Pred A p) (Q : Pred A q) → P ⊆ Q → Empty (P ∖ Q)
⊆→Empty-∖ P Q p→q x (p , ¬q) = ¬q (p→q p)
Empty-∖⇔⊆ : (P : Pred A p) → {Q : Pred A q} → Decidable Q → Empty (P ∖ Q) ⇔ P ⊆ Q
Empty-∖⇔⊆ P {Q} Q? = mk⇔ (Empty-∖→⊆ P Q?) (⊆→Empty-∖ P Q)

-- TODO: Is Maybe→Pred used? Use Maybe's Any instead.
Maybe→Pred : (_≈_ : REL A B ℓ₁) → Maybe A → Pred B ℓ₁
Maybe→Pred _≈_ (just x) y = x ≈ y
Maybe→Pred _≈_ nothing y = Poly.⊥
Maybe→Pred-map : (f : A → B) (_≈_ : REL B C ℓ₁) (mx : Maybe A) →
                 Maybe→Pred _≈_ (Maybe.map f mx) ≡ Maybe→Pred (λ x → f x ≈_) mx
Maybe→Pred-map f _≈_ (just x) = refl
Maybe→Pred-map f _≈_ nothing = refl

right-unique→⊆ : {ℓA ℓN ℓP ℓQ : Level} {A : Set ℓA}
     {N : Set ℓN} {P : Pred A ℓP} {Q : Pred A ℓQ}
     (sum : N ⊎ (∃ λ x → P x × Q x)) →
     ((x : A) → P x → ¬ N) →
     ((x1 x2 : A) → P x1 → P x2 → x1 ≡ x2) →
     P ⊆ Q
right-unique→⊆ {N = N} {P} {Q} sum P→¬N P→eq {x} Px with sum
... | inj₁ n = ⊥-elim (P→¬N x Px n)
... | inj₂ (x′ , Px′ , Qx′) with P→eq x x′ Px Px′
...   | refl = Qx′

right-unique→≐ : {ℓA ℓN ℓP ℓQ : Level} {A : Set ℓA}
     {N : Set ℓN} {P : Pred A ℓP} {Q : Pred A ℓQ}
     (sum : N ⊎ (∃ λ x → P x × Q x)) →
     ((x : A) → P x → ¬ N) → ((x : A) → Q x → ¬ N) →
     ((x1 x2 : A) → P x1 → P x2 → x1 ≡ x2) →
     ((x1 x2 : A) → Q x1 → Q x2 → x1 ≡ x2) →
     P ≐ Q
right-unique→≐ sum P→¬N Q→¬N P→eq Q→eq =
    right-unique→⊆ sum P→¬N P→eq
  , right-unique→⊆ sum-swap Q→¬N Q→eq
  where
  sum-swap = ⊎.map₂ (×.map₂ ×.swap) sum

-- TODO: This and its Lookup user seem messy.
--       Is there a more straightforward way?
Maybe-right-unique→≐ : {ℓA ℓC ℓP : Level} {A : Set ℓA}
     {C : Set ℓC} {P : Pred A ℓP}
     {ma : Maybe A}
     (sum : (ma ≡ nothing × C) ⊎ (∃ λ x → (ma ≡ just x × P x))) →
     ((x : A) → P x → ¬ C) →
     ((x1 x2 : A) → P x1 → P x2 → x1 ≡ x2) →
     ((ma ≡_) ∘ just) ≐ P
Maybe-right-unique→≐ {C = C} {P} {ma} sum P→¬C x-eq =
  right-unique→≐
    {N = (ma ≡ nothing × C)} {P = ((ma ≡_) ∘ just)} {Q = P}
    sum
    (λ{ _ () (refl , _)})
    (λ x Px → P→¬C x Px ∘ proj₂)
    (λ{ x1 x2 refl eq → just-injective eq})
    x-eq

data ⇔≐ {ℓA ℓB ℓP ℓQ : Level} {A : Set ℓA} {B : Set ℓB}
        (⇔Dom : A ⇔ B) (P : Pred A ℓP) (Q : Pred B ℓQ)
       : Set (ℓA ⊔ ℓB ⊔ ℓP ⊔ ℓQ) where
  mk⇔≐ : ((x : A) → P x → Q (Equivalence.to ⇔Dom x)) →
         ((y : B) → Q y → P (Equivalence.from ⇔Dom y)) →
         ⇔≐ ⇔Dom P Q

-- TODO: Move to Ponens.Relations.Binary
_⇔_Respects_ : (A → Set ℓ₁) → (B → Set ℓ₂) → REL A B ℓ₃ → Set _
P ⇔ Q Respects _∼_ = ∀ {x y} → x ∼ y → P x ⇔ Q y
