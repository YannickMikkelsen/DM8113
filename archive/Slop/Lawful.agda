module Slop.Lawful where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Slop.Hexc
open Functor ⦃...⦄

-- Det Gen skal vide om en signatur-funktor Σ udover at den er en Functor:
--  All Q x     : alle børn i x opfylder Q
--  fmap-∘      : fmap er funktoriel (kun ∘-loven bruges)
--  all-cong    : fmap h₁ x ≡ fmap h₂ x, hvis h₁ ≡ h₂ på alle børn
record Lawful (Σ : Set₁ → Set₁) ⦃ fΣ : Functor Σ ⦄ : Set₂ where
  field
    All      : ∀ {X : Set₁} → (X → Set₁) → Σ X → Set₁
    fmap-∘   : ∀ {X Y Z : Set₁} (g : Y → Z) (f : X → Y) (x : Σ X)
             → fmap g (fmap f x) ≡ fmap (λ a → g (f a)) x
    all-cong : ∀ {X Y : Set₁} (Q : X → Set₁) (h₁ h₂ : X → Y) (x : Σ X)
             → All Q x → (∀ a → Q a → h₁ a ≡ h₂ a)
             → fmap h₁ x ≡ fmap h₂ x

-- Summen af to lovlige funktorer er lovlig
lawful+ : ∀ {F G : Set₁ → Set₁} ⦃ fF : Functor F ⦄ ⦃ fG : Functor G ⦄
        → Lawful F → Lawful G → Lawful (F + G)
lawful+ {F} {G} ⦃ fF ⦄ ⦃ fG ⦄ lF lG = record
  { All      = All+
  ; fmap-∘   = fmap-∘+
  ; all-cong = all-cong+
  }
  where
    module LF = Lawful lF
    module LG = Lawful lG

    All+ : ∀ {X : Set₁} → (X → Set₁) → (F + G) X → Set₁
    All+ Q (i₁ x) = LF.All Q x
    All+ Q (i₂ y) = LG.All Q y

    fmap-∘+ : ∀ {X Y Z : Set₁} (g : Y → Z) (f : X → Y) (x : (F + G) X)
            → fmap g (fmap f x) ≡ fmap (λ a → g (f a)) x
    fmap-∘+ g f (i₁ x) = cong i₁ (LF.fmap-∘ g f x)
    fmap-∘+ g f (i₂ y) = cong i₂ (LG.fmap-∘ g f y)

    all-cong+ : ∀ {X Y : Set₁} (Q : X → Set₁) (h₁ h₂ : X → Y) (x : (F + G) X)
              → All+ Q x → (∀ a → Q a → h₁ a ≡ h₂ a)
              → fmap h₁ x ≡ fmap h₂ x
    all-cong+ Q h₁ h₂ (i₁ x) a c = cong i₁ (LF.all-cong Q h₁ h₂ x a c)
    all-cong+ Q h₁ h₂ (i₂ y) a c = cong i₂ (LG.all-cong Q h₁ h₂ y a c)