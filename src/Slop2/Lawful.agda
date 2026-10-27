module Slop2.Lawful where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Slop2.Hexc
open Functor ⦃...⦄

-- "Alle børn opfylder Q" for en funktor Σ, med kongruens under fmap
record Lawful (Σ : Set₁ → Set₁) ⦃ _ : Functor Σ ⦄ : Set₂ where
  field
    All     : ∀ {X : Set₁} → (X → Set₁) → Σ X → Set₁
    all-ext : ∀ {X Y : Set₁} {Q : X → Set₁} {x : Σ X}
            → All Q x → (h₁ h₂ : X → Y)
            → (∀ t → Q t → h₁ t ≡ h₂ t)
            → fmap h₁ x ≡ fmap h₂ x
    fmap-∘  : ∀ {X Y Z : Set₁} (g : Y → Z) (f : X → Y) (x : Σ X)
            → fmap (λ t → g (f t)) x ≡ fmap g (fmap f x)

lawful+ : ∀ {F G : Set₁ → Set₁} ⦃ _ : Functor F ⦄ ⦃ _ : Functor G ⦄
        → Lawful F → Lawful G → Lawful (F + G)
lawful+ {F} {G} LF LG = record { All = All+ ; all-ext = ext+ ; fmap-∘ = comp+ }
  where
  All+ : ∀ {X : Set₁} → (X → Set₁) → (F + G) X → Set₁
  All+ Q (i₁ x) = Lawful.All LF Q x
  All+ Q (i₂ y) = Lawful.All LG Q y

  ext+ : ∀ {X Y : Set₁} {Q : X → Set₁} {x : (F + G) X}
       → All+ Q x → (h₁ h₂ : X → Y)
       → (∀ t → Q t → h₁ t ≡ h₂ t)
       → fmap h₁ x ≡ fmap h₂ x
  ext+ {x = i₁ x} a h₁ h₂ e = cong i₁ (Lawful.all-ext LF a h₁ h₂ e)
  ext+ {x = i₂ y} a h₁ h₂ e = cong i₂ (Lawful.all-ext LG a h₁ h₂ e)

  comp+ : ∀ {X Y Z : Set₁} (g : Y → Z) (f : X → Y) (x : (F + G) X)
        → fmap (λ t → g (f t)) x ≡ fmap g (fmap f x)
  comp+ g f (i₁ x) = cong i₁ (Lawful.fmap-∘ LF g f x)
  comp+ g f (i₂ y) = cong i₂ (Lawful.fmap-∘ LG g f y)