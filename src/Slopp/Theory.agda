module Slopp.Theory where

-- En algebraisk teori over en signatur Σ er en mængde af ligninger.
-- Her er en teori et prædikat på ligninger ("er aksiom"), så en teori
-- kan samles som en induktiv familie. En model er en algebra, der
-- respekterer alle aksiomerne. Alt er udtrykt med Free (ingen Term).
-- IKKE typechecket.

open import Level using (suc; zero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Sum using (_⊎_; inj₁; inj₂)


open import Slopp.PHexc
open import Slopp.Lawful
open import Slopp.PExcGen

open Functor ⦃...⦄

-- Teori over Σ: hvilke ligninger (med vilkårligt Γ, A, i, j) er aksiomer
Theory : ∀ {I : Set} → ((I → I → Set₁) → (I → I → Set₁)) → Set₂
Theory {I} Σ = ∀ {i j : I} {Γ A : Set₁} → Equation Σ Γ A i j → Set₁

-- (C, alg) er en model af T, hvis alle aksiomer med slutindeks j₀ respekteres
Models : ∀ {I : Set} {Σ : (I → I → Set₁) → (I → I → Set₁)} ⦃ _ : Functor Σ ⦄
           (T : Theory Σ) {C : I → I → Set₁} {j₀ : I}
       → (∀ {a} → Σ C a j₀ → C a j₀) → Set₂
Models {I} {Σ} T {C} {j₀} alg =
  ∀ {i : I} {Γ A : Set₁} (e : Equation Σ Γ A i j₀) → T e → respects alg e




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

    ~bind  : ∀ {B : Set₁} {i j l} {m m' : Free Σ B i j}
               {k k' : B → Free Σ A j l}
           → m ~ m' → (∀ x → k x ~ k' x)
           → (m >>= k) ~ (m' >>= k')
------------------------------------------------------------------------


_∪_ : ∀ {I : Set} {Σ : (I → I → Set₁) → (I → I → Set₁)}
    → Theory Σ → Theory Σ → Theory Σ
(T₁ ∪ T₂) e = T₁ e ⊎ T₂ e

∪-model : ∀ {I : Set} {Σ : (I → I → Set₁) → (I → I → Set₁)} ⦃ _ : Functor Σ ⦄
            (T₁ T₂ : Theory Σ) {C : I → I → Set₁} {j₀ : I}
            {alg : ∀ {a} → Σ C a j₀ → C a j₀}
        → Models T₁ alg → Models T₂ alg → Models (T₁ ∪ T₂) alg
∪-model T₁ T₂ m₁ m₂ e (inj₁ t) = m₁ e t
∪-model T₁ T₂ m₁ m₂ e (inj₂ t) = m₂ e t

_⊗⟨_⟩_ : ∀ {I} {Σ : (I → I → Set₁) → (I → I → Set₁)} → Theory Σ → Theory Σ → Theory Σ → Theory Σ
T₁ ⊗⟨ Comm ⟩ T₂ = (T₁ ∪ T₂) ∪ Comm

⊗-model : ∀ {I : Set} {Σ : (I → I → Set₁) → (I → I → Set₁)} ⦃ _ : Functor Σ ⦄
            (T₁ T₂ Comm : Theory Σ) {C : I → I → Set₁} {j₀ : I}
            {alg : ∀ {a} → Σ C a j₀ → C a j₀}
        → Models T₁ alg → Models T₂ alg → Models Comm alg
        → Models (T₁ ⊗⟨ Comm ⟩ T₂) alg
⊗-model T₁ T₂ Comm m₁ m₂ mc =
  ∪-model (T₁ ∪ T₂) Comm (∪-model T₁ T₂ m₁ m₂) mc
------------------------------------------------------------------------
-- Teorien for Exc: lovene fra Gen (de ubetingede)

module ExcTheory {I : Set}
                 (Σ : (I → I → Set₁) → (I → I → Set₁)) ⦃ fΣ : Functor Σ ⦄
                 (L : Lawful Σ)
                 (i₀ j₀ k₀ m₀ : I)
                 (D : I → I → Set₁)
                 (αD : ∀ {a} → Σ D a j₀ → D a j₀) where

  open Gen Σ L i₀ j₀ k₀ m₀ D αD

  data ExcAx : ∀ {i j : I} {Γ A : Set₁} → Equation S Γ A i j → Set₁ where
    ax-catch-end    : ∀ X   → ExcAx (eq-Catch-End X)
    ax-catch-throw  : ∀ X   → ExcAx (eq-Catch-Throw X)
    ax-end-through  : ∀ X   → ExcAx (eq-end-through X)
    ax-catch-bind   : ∀ X   → ExcAx (eq3 X)
    ax-bind-end     : ∀ X W → ExcAx (eq-Bind-lovene X W)
    ax-throw-bind   : ∀ X   → ExcAx (eq-Throw-Bind X)
    ax-catch-distr  : ∀ X W → ExcAx (eq-Catch-Distr X W)

  -- algE er en model af Exc-teorien: beviserne er de -ok-lemmaer, vi allerede har
  excModel : Models {Σ = S} ExcAx {C = C} {j₀ = j₀} algE
  excModel _ (ax-catch-end X)     = eq-Catch-End-ok X
  excModel _ (ax-catch-throw X)   = eq-Catch-Throw-ok X
  excModel _ (ax-end-through X)   = eq-end-through-ok X
  excModel _ (ax-catch-bind X)    = eq3-ok X
  excModel _ (ax-bind-end X W)    = eq-Bind-lovene-ok X W
  excModel _ (ax-throw-bind X)    = eq-Throw-Bind-ok X
  excModel _ (ax-catch-distr X W) = eq-Catch-Distr-ok X W