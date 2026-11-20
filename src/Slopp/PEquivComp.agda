module Slopp.PEquivComp where

open import Level using (suc; zero; Lift; lower)
open import Slopp.PHexc2
open Functor ⦃...⦄

Theory : ∀ {I : Set} (Σ : (I → I → Set₁) → (I → I → Set₁)) → Set₂
Theory {I} Σ = ∀ {Γ A : Set₁} {i j : I} → Equation Σ Γ A i j → Set₁

liftΓ : ∀ {I : Set} {Σ : (I → I → Set₁) → (I → I → Set₁)}
          {Γ : Set} {A : Set₁} {i j : I}
      → Equation Σ Γ A i j
      → Equation Σ (Lift (suc zero) Γ) A i j
liftΓ (l ≐ r) = (λ g → l (lower g)) ≐ (λ g → r (lower g))

module EquivalentComputations
         {I : Set} {Σ : (I → I → Set₁) → (I → I → Set₁)}
         ⦃ _ : Functor Σ ⦄ (T : Theory Σ) where

  infix 4 _~_

  data _~_ {A : Set₁} : ∀ {i j : I} → Free Σ A i j → Free Σ A i j → Set₂ where
    ~refl  : ∀ {i j} {c : Free Σ A i j} → c ~ c

    ~sym   : ∀ {i j} {c d : Free Σ A i j} → c ~ d → d ~ c

    ~trans : ∀ {i j} {c d e : Free Σ A i j} → c ~ d → d ~ e → c ~ e

    ~cong  : ∀ {i j j' : I} (o : Σ (Free Σ A) i j) (k k' : ∀ {a} → Free Σ A a j → Free Σ A a j')
           → (∀ {a} (x : Free Σ A a j) → k x ~ k' x)
           → op (fmap k o) ~ op (fmap k' o)

    ~eq    : ∀ {Γ B : Set₁} {i j m : I} {e : Equation Σ Γ B i j}
           → T e → (g : Γ) (k : B → Free Σ A j m)
           → (lhs e g >>= k) ~ (rhs e g >>= k)
    ~eq₀   : ∀ {Γ B : Set₁} {i j : I} {e : Equation Σ Γ A i j}
           → T e → (g : Γ) → lhs e g ~ rhs e g