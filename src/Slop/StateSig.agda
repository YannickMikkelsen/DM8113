module Slop.StateSig where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Slop.Hexc
open import Slop.Lawful
open Functor ⦃...⦄

variable
  S     : Set
  X Y Z : Set₁

data StateOp (S : Set) (K : Set₁) : Set₁ where
  get : (S → K) → StateOp S K
  put : S → K → StateOp S K

instance
  fState : Functor (StateOp S)
  fState .fmap f (get k)   = get (λ s → f (k s))
  fState .fmap f (put s k) = put s (f k)

AllSt : (X → Set₁) → StateOp S X → Set₁
AllSt Q (get k)   = ∀ s → Q (k s)
AllSt Q (put s k) = Q k

fmap-∘St : (g : Y → Z) (f : X → Y) (op : StateOp S X) → fmap g (fmap f op) ≡ fmap (λ a → g (f a)) op
fmap-∘St g f (get k)   = refl
fmap-∘St g f (put s k) = refl

all-congSt : (Q : X → Set₁) (h₁ h₂ : X → Y) (op : StateOp S X) 
            → AllSt Q op 
            → (∀ a → Q a → h₁ a ≡ h₂ a) 
            → fmap h₁ op ≡ fmap h₂ op
all-congSt Q h₁ h₂ (get k)   a c = cong get (funext (λ s → c (k s) (a s)))
all-congSt Q h₁ h₂ (put s k) a c = cong (put s) (c k a)


open Lawful
lawfulState : Lawful (StateOp S)
lawfulState .All = AllSt
lawfulState .fmap-∘ = fmap-∘St
lawfulState .all-cong = all-congSt


-- lawfulState = record { All = AllSt ; fmap-∘ = fmap-∘St ; all-cong = all-congSt }
