module Slop.EquivComp where

open import Level using (suc; zero; Lift; lower)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Slop.Hexc
open Functor ⦃...⦄

-- Definition 3.1 (EquivalentComputations)
Theory : (Σ : Set₁ → Set₁) → Set₂
Theory Σ = ∀ {Γ V : Set₁} → Equation Σ Γ V → Set₁

Models : ∀ {Σ : Set₁ → Set₁} {C : Set₁} ⦃ _ : Functor Σ ⦄ → Theory Σ → (Σ C → C) → Set₂
Models {Σ} T alg = ∀ {Γ V : Set₁} {e : Equation Σ Γ V} → T e → respects alg e

liftΓ : ∀ {Σ : Set₁ → Set₁} {V : Set₁} {Γ : Set}
      → Equation Σ Γ V 
      → Equation Σ (Lift (suc zero) Γ) V
liftΓ (l ≐ r) = (λ g → l (lower g)) ≐ (λ g → r (lower g))

liftΓ-ok : ∀ {Σ : Set₁ → Set₁} {V C : Set₁} {Γ : Set} ⦃ _ : Functor Σ ⦄
             {alg : Σ C → C} {e : Equation Σ Γ V}
         → respects alg e → respects alg (liftΓ e)
liftΓ-ok ok ρ g = ok ρ (lower g)

module EquivalentComputations
         {Σ : Set₁ → Set₁} ⦃ _ : Functor Σ ⦄
         (fmap-∘ : ∀ {X Y Z : Set₁} (g : Y → Z) (f : X → Y) (x : Σ X)
                 → fmap g (fmap f x) ≡ fmap (λ a → g (f a)) x)
         (T : Theory Σ) where

  infix 4 _~_

  data _~_ {A : Set₁} : Free Σ A → Free Σ A → Set₂ where
    ~refl  : ∀ {c} → c ~ c
    ~sym   : ∀ {c d} → c ~ d → d ~ c
    ~trans : ∀ {c d e} → c ~ d → d ~ e → c ~ e
    ~cong  : ∀ {X : Set₁} (o : Σ X) (k k' : X → Free Σ A)
           → (∀ x → k x ~ k' x)
           → op (fmap k o) ~ op (fmap k' o)
    ~eq    : ∀ {Γ V : Set₁} {e : Equation Σ Γ V}
           → T e → (g : Γ) (k : V → Free Σ A)
           → (lhs e g >>= k) ~ (rhs e g >>= k)

  {-# TERMINATING #-}
  fold-bind : ∀ {V A C : Set₁} (ρ : A → C) (alg : Σ C → C)
                (t : Free Σ V) (k : V → Free Σ A)
            → fold ρ alg (t >>= k) ≡ fold (λ v → fold ρ alg (k v)) alg t
  fold-bind ρ alg (pure v) k = refl
  fold-bind ρ alg (op x)   k =
    cong alg
      (trans (fmap-∘ (fold ρ alg) (_>>= k) x)
             (cong (λ h → fmap h x)
                   (funext (λ a → fold-bind ρ alg a k))))

  soundness : ∀ {A C : Set₁} {alg : Σ C → C}
            → Models T alg
            → ∀ {c d : Free Σ A}
            → c ~ d
            → ∀ (ρ : A → C) → fold ρ alg c ≡ fold ρ alg d
  soundness mod ~refl              ρ = refl
  soundness mod (~sym p)           ρ = sym (soundness mod p ρ)
  soundness mod (~trans p q)       ρ = trans (soundness mod p ρ) (soundness mod q ρ)
  soundness {alg = alg} mod (~cong o k k' ih) ρ =
    cong alg
      (trans (fmap-∘ (fold ρ alg) k o)
             (trans (cong (λ h → fmap h o)
                          (funext (λ x → soundness mod (ih x) ρ)))
                    (sym (fmap-∘ (fold ρ alg) k' o))))
  soundness {alg = alg} mod (~eq {e = e} te g k) ρ =
    trans (fold-bind ρ alg (lhs e g) k)
          (trans (mod te (λ v → fold ρ alg (k v)) g)
                 (sym (fold-bind ρ alg (rhs e g) k)))