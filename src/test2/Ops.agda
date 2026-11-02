module Slop2.Ops where

open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Slop2.Hexc
open import Slop2.Lawful
open Functor ⦃...⦄

------------------------------------------------------------------------
-- State

data StateOp (S : Set) (K : Set₁) : Set₁ where
  get : (S → K) → StateOp S K
  put : S → K → StateOp S K

instance
  fStateOp : ∀ {S} → Functor (StateOp S)
  fStateOp = record { fmap = λ where
    f (get k)   → get (λ s → f (k s))
    f (put s m) → put s (f m) }

All-St : ∀ {S} {X : Set₁} → (X → Set₁) → StateOp S X → Set₁
All-St Q (get k)   = ∀ s → Q (k s)
All-St Q (put s m) = Q m

ext-St : ∀ {S} {X Y : Set₁} {Q : X → Set₁} {x : StateOp S X}
       → All-St Q x → (h₁ h₂ : X → Y)
       → (∀ t → Q t → h₁ t ≡ h₂ t)
       → fmap h₁ x ≡ fmap h₂ x
ext-St {x = get k}   a h₁ h₂ e = cong get (funext (λ s → e (k s) (a s)))
ext-St {x = put s m} a h₁ h₂ e = cong (put s) (e m a)

comp-St : ∀ {S} {X Y Z : Set₁} (g : Y → Z) (f : X → Y) (x : StateOp S X)
        → fmap (λ t → g (f t)) x ≡ fmap g (fmap f x)
comp-St g f (get k)   = refl
comp-St g f (put s m) = refl

lawful-St : ∀ {S} → Lawful (StateOp S)
lawful-St = record { All = All-St ; all-ext = ext-St ; fmap-∘ = comp-St }

------------------------------------------------------------------------
-- Fil

data FileOpS (K : Set₁) : Set₁ where
  fopen  : String → K → FileOpS K
  fread  : (String → K) → FileOpS K
  fwrite : String → K → FileOpS K
  fclose : K → FileOpS K

instance
  fFileOpS : Functor FileOpS
  fFileOpS = record { fmap = λ where
    f (fopen p k)  → fopen p (f k)
    f (fread k)    → fread (λ r → f (k r))
    f (fwrite w k) → fwrite w (f k)
    f (fclose k)   → fclose (f k) }

All-F : ∀ {X : Set₁} → (X → Set₁) → FileOpS X → Set₁
All-F Q (fopen _ m)  = Q m
All-F Q (fread k)    = ∀ r → Q (k r)
All-F Q (fwrite _ m) = Q m
All-F Q (fclose m)   = Q m

ext-F : ∀ {X Y : Set₁} {Q : X → Set₁} {x : FileOpS X}
      → All-F Q x → (h₁ h₂ : X → Y)
      → (∀ t → Q t → h₁ t ≡ h₂ t)
      → fmap h₁ x ≡ fmap h₂ x
ext-F {x = fopen p m}  a h₁ h₂ e = cong (fopen p) (e m a)
ext-F {x = fread k}    a h₁ h₂ e = cong fread (funext (λ r → e (k r) (a r)))
ext-F {x = fwrite w m} a h₁ h₂ e = cong (fwrite w) (e m a)
ext-F {x = fclose m}   a h₁ h₂ e = cong fclose (e m a)

comp-F : ∀ {X Y Z : Set₁} (g : Y → Z) (f : X → Y) (x : FileOpS X)
       → fmap (λ t → g (f t)) x ≡ fmap g (fmap f x)
comp-F g f (fopen p m)  = refl
comp-F g f (fread k)    = refl
comp-F g f (fwrite w m) = refl
comp-F g f (fclose m)   = refl

lawful-F : Lawful FileOpS
lawful-F = record { All = All-F ; all-ext = ext-F ; fmap-∘ = comp-F }