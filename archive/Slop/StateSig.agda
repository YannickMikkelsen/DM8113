module Slop.StateSig where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Slop.Hexc
open import Slop.Lawful
open Functor ⦃...⦄

data StateOp (S : Set) (K : Set₁) : Set₁ where
  get : (S → K) → StateOp S K
  put : S → K → StateOp S K

instance
  fState : ∀ {S} → Functor (StateOp S)
  fState = record { fmap = λ where
    f (get k)   → get (λ s → f (k s))
    f (put s k) → put s (f k) }

AllSt : ∀ {S : Set} {X : Set₁} → (X → Set₁) → StateOp S X → Set₁
AllSt Q (get k)   = ∀ s → Q (k s)
AllSt Q (put s k) = Q k

fmap-∘St : ∀ {S : Set} {X Y Z : Set₁} (g : Y → Z) (f : X → Y) (x : StateOp S X)
         → fmap g (fmap f x) ≡ fmap (λ a → g (f a)) x
fmap-∘St g f (get k)   = refl
fmap-∘St g f (put s k) = refl

all-congSt : ∀ {S : Set} {X Y : Set₁} (Q : X → Set₁) (h₁ h₂ : X → Y) (x : StateOp S X)
           → AllSt Q x → (∀ a → Q a → h₁ a ≡ h₂ a) → fmap h₁ x ≡ fmap h₂ x
all-congSt Q h₁ h₂ (get k)   a c = cong get (funext (λ s → c (k s) (a s)))
all-congSt Q h₁ h₂ (put s k) a c = cong (put s) (c k a)

lawfulState : ∀ {S : Set} → Lawful (StateOp S)
lawfulState = record { All = AllSt ; fmap-∘ = fmap-∘St ; all-cong = all-congSt }