module Slop.FHAlg where

open import Data.String  using (String)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Slop.Hexc
open import Slop.Lawful
open Functor ⦃...⦄

-- Én konstruktør pr. operation, ingen Opr
data FileOpS (K : Set₁) : Set₁ where
  fopen  : String → K → FileOpS K
  fread  : (String → K) → FileOpS K
  fwrite : String → K → FileOpS K
  fclose : K → FileOpS K

instance
  fFile : Functor FileOpS
  fFile = record { fmap = λ where
    f (fopen p k)  → fopen p (f k)
    f (fread k)    → fread (λ s → f (k s))
    f (fwrite s k) → fwrite s (f k)
    f (fclose k)   → fclose (f k) }

-- Semantik: tilstanden er kun filens indhold (som før)
HFile : Set₁ → Set₁
HFile R = String → R × String

algFile : ∀ {R : Set₁} → FileOpS (HFile R) → HFile R
algFile (fopen _ k)  m = k m
algFile (fread k)    m = k m m
algFile (fwrite s k) m = k s        -- overskriver
algFile (fclose k)   m = k m

AllFile : ∀ {X : Set₁} → (X → Set₁) → FileOpS X → Set₁
AllFile Q (fopen _ k)  = Q k
AllFile Q (fread k)    = ∀ s → Q (k s)
AllFile Q (fwrite _ k) = Q k
AllFile Q (fclose k)   = Q k

fmap-∘File : ∀ {X Y Z : Set₁} (g : Y → Z) (f : X → Y) (x : FileOpS X)
           → fmap g (fmap f x) ≡ fmap (λ a → g (f a)) x
fmap-∘File g f (fopen _ k)  = refl
fmap-∘File g f (fread k)    = refl
fmap-∘File g f (fwrite _ k) = refl
fmap-∘File g f (fclose k)   = refl

all-congFile : ∀ {X Y : Set₁} (Q : X → Set₁) (h₁ h₂ : X → Y) (x : FileOpS X)
             → AllFile Q x → (∀ a → Q a → h₁ a ≡ h₂ a) → fmap h₁ x ≡ fmap h₂ x
all-congFile Q h₁ h₂ (fopen p k)  a c = cong (fopen p) (c k a)
all-congFile Q h₁ h₂ (fread k)    a c = cong fread (funext (λ s → c (k s) (a s)))
all-congFile Q h₁ h₂ (fwrite s k) a c = cong (fwrite s) (c k a)
all-congFile Q h₁ h₂ (fclose k)   a c = cong fclose (c k a)

lawfulFile : Lawful FileOpS
lawfulFile = record { All = AllFile ; fmap-∘ = fmap-∘File ; all-cong = all-congFile }