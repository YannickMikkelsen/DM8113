module Slopp.Theory where

-- En algebraisk teori over en signatur Σ er en mængde af ligninger.
-- Her er en teori et prædikat på ligninger ("er aksiom"), så en teori
-- kan samles som en induktiv familie. En model er en algebra, der
-- respekterer alle aksiomerne. Alt er udtrykt med Free (ingen Term).
-- IKKE typechecket.

open import Level using (suc; zero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Slopp.PHexc
open import Slopp.Lawful
open import Slopp.PExcGen

-- Teori over Σ: hvilke ligninger (med vilkårligt Γ, A, i, j) er aksiomer
Theory : ∀ {I : Set} → ((I → I → Set₁) → (I → I → Set₁)) → Set₂
Theory {I} Σ = ∀ {i j : I} {Γ A : Set₁} → Equation Σ Γ A i j → Set₁

-- (C, alg) er en model af T, hvis alle aksiomer med slutindeks j₀ respekteres
Models : ∀ {I : Set} {Σ : (I → I → Set₁) → (I → I → Set₁)} ⦃ _ : Functor Σ ⦄
           (T : Theory Σ) {C : I → I → Set₁} {j₀ : I}
       → (∀ {a} → Σ C a j₀ → C a j₀) → Set₂
Models {I} {Σ} T {C} {j₀} alg =
  ∀ {i : I} {Γ A : Set₁} (e : Equation Σ Γ A i j₀) → T e → respects alg e

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