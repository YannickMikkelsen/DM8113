module Pmonad where
open import Data.Unit    using (⊤; tt)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.Char using (Char)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Function using (_∘_)
open import Data.String  using (String)
open import Data.Product using (Σ; proj₁; proj₂)


data OC : Set where
  Open : OC
  Closed : OC

data SOC : OC → Set where
  SOpen : SOC Open
  SCLosed : SOC Closed

State : Set
State = ℕ × OC

StateM : Set → Set → Set → Set
StateM i j A = State → Maybe (A × State)

record PMonad {I : Set} {M : I → I → Set → Set} : Set₁ where
  field
    pure : ∀ {i} {A : Set} → A → M i i A
    _>>=_ : ∀ {i j k} {A B : Set} → M i j A → (A → M j k B) → M i k B

ProjL : Set → Set → Set
ProjL I A = I → A

ProjF : Set → OC → Set
ProjF I S = I → SOC S

InjL : Set → Set → Set
InjL I A = I → A

InjF : Set → OC → Set → Set
InjF I S J = I → SOC S → J

record LS {I : Set} {M : I → I → Set → Set} (a : Set) : Set₁ where
  field
    pmonad : PMonad {I} {M}
  open PMonad pmonad public
  field
    look : ∀ {i : I} → ProjL I a → M i i a
    set  : ∀ {i j : I} → InjL I a → a → M i j ⊤

