module Slopp.Lawful where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Slopp.PHexc
open Functor ⦃...⦄

-- Det Gen skal vide om en signatur-funktor Σ udover at den er en Functor:
--  All Q x     : alle børn i x opfylder Q
--  fmap-∘      : fmap er funktoriel (kun ∘-loven bruges)
--  all-cong    : fmap h₁ x ≡ fmap h₂ x, hvis h₁ ≡ h₂ på alle børn
record Lawful {I : Set} (Σ : (I → I → Set₁) → (I → I → Set₁))
              ⦃ _ : Functor Σ ⦄ : Set₂ where
  field
    All      : ∀ {X : I → I → Set₁} {i j}
             → (∀ {a} → X a j → Set₁) → Σ X i j → Set₁

    fmap-∘   : ∀ {X Y Z : I → I → Set₁} {j j' j''}
               (g : ∀ {i} → Y i j' → Z i j'')
               (f : ∀ {i} → X i j → Y i j')
               {i} (x : Σ X i j)
             → fmap {X = Y} {Y = Z} {j = j'} {j' = j''} g
                 (fmap {X = X} {Y = Y} {j = j} {j' = j'} f x)
               ≡ fmap {X = X} {Y = Z} {j = j} {j' = j''} (λ {a} v → g (f v)) x

    all-cong : ∀ {X Y : I → I → Set₁} {j j'}
               (Q : ∀ {a} → X a j → Set₁)
               (h₁ h₂ : ∀ {i} → X i j → Y i j')
               {i} (x : Σ X i j)
             → All {X} {i} {j} Q x
             → (∀ {a} (v : X a j) → Q {a} v → h₁ {a} v ≡ h₂ {a} v)
             → fmap {X = X} {Y = Y} {j = j} {j' = j'} h₁ x
               ≡ fmap {X = X} {Y = Y} {j = j} {j' = j'} h₂ x

-- Summen af to lovlige funktorer er lovlig
lawful+ : ∀ {I : Set} {F G : (I → I → Set₁) → (I → I → Set₁)}
            ⦃ fF : Functor F ⦄ ⦃ fG : Functor G ⦄
        → Lawful F → Lawful G → Lawful (F + G)
lawful+ {I = I} {F = F} {G = G} ⦃ fF ⦄ ⦃ fG ⦄ lF lG = record
  { All      = All+
  ; fmap-∘   = fmap-∘+
  ; all-cong = all-cong+
  }
  where
    module LF = Lawful lF
    module LG = Lawful lG

    All+ : ∀ {X : I → I → Set₁} {i j}
         → (∀ {a} → X a j → Set₁) → (F + G) X i j → Set₁
    All+ {X} {i} {j} Q (i₁ x) = LF.All {X} {i} {j} Q x
    All+ {X} {i} {j} Q (i₂ y) = LG.All {X} {i} {j} Q y

    fmap-∘+ : ∀ {X Y Z : I → I → Set₁} {j j' j''}
              (g : ∀ {i} → Y i j' → Z i j'')
              (f : ∀ {i} → X i j → Y i j')
              {i} (x : (F + G) X i j)
            → fmap {X = Y} {Y = Z} {j = j'} {j' = j''} g
                (fmap {X = X} {Y = Y} {j = j} {j' = j'} f x)
              ≡ fmap {X = X} {Y = Z} {j = j} {j' = j''} (λ {a} v → g (f v)) x
    fmap-∘+ {X} {Y} {Z} {j} {j'} {j''} g f {i} (i₁ x) =
      cong i₁ (LF.fmap-∘ {X} {Y} {Z} {j} {j'} {j''} g f {i} x)
    fmap-∘+ {X} {Y} {Z} {j} {j'} {j''} g f {i} (i₂ y) =
      cong i₂ (LG.fmap-∘ {X} {Y} {Z} {j} {j'} {j''} g f {i} y)

    all-cong+ : ∀ {X Y : I → I → Set₁} {j j'}
                (Q : ∀ {a} → X a j → Set₁)
                (h₁ h₂ : ∀ {i} → X i j → Y i j')
                {i} (x : (F + G) X i j)
              → All+ {X} {i} {j} Q x
              → (∀ {a} (v : X a j) → Q {a} v → h₁ {a} v ≡ h₂ {a} v)
              → fmap {X = X} {Y = Y} {j = j} {j' = j'} h₁ x
                ≡ fmap {X = X} {Y = Y} {j = j} {j' = j'} h₂ x
    all-cong+ {X} {Y} {j} {j'} Q h₁ h₂ {i} (i₁ x) a c =
      cong i₁ (LF.all-cong {X} {Y} {j} {j'} Q h₁ h₂ {i} x a c)
    all-cong+ {X} {Y} {j} {j'} Q h₁ h₂ {i} (i₂ y) a c =
      cong i₂ (LG.all-cong {X} {Y} {j} {j'} Q h₁ h₂ {i} y a c)