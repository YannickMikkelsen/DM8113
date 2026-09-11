module Pmonad.Pmonad where
open import Data.Unit    using (⊤; tt)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.Char using (Char)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Function using (_∘_)
open import Data.String  using (String)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; Σ-syntax; _,_)


data OC : Set where
  Open : OC
  Closed : OC

data SOC : OC → Set where
  SOpen : SOC Open
  SCLosed : SOC Closed

State : Set
State = ℕ × OC 


record PMonad {I : Set} {M : I → I → Set → Set} : Set₁ where
  field
    pure : ∀ {i} {A : Set} → A → M i i A
    _>>=_ : ∀ {i j k} {A B : Set} → M i j A → (A → M j k B) → M i k B


ProjL : Set → Set → Set
ProjL I A = I → A

ProjF : Set → OC → Set
ProjF I S = I → SOC S

InjL : Set → Set → Set → Set
InjL I A J = I → A → J

InjF : Set → OC → Set → Set
InjF I S J = I → SOC S → J



record Combined {I : Set} {M : I → I → Set → Set} : Set₁ where
  field
    pmonad : PMonad {I} {M}
  open PMonad pmonad public
  field
    look : ∀ {i : I} {a : Set} → ProjL I a → M i i a
    set  : ∀ {i j : I} {a : Set} → InjL I a I → M i j ⊤
    fopen : ∀ {i j : I} → ProjF I Closed → InjF I Open I →  M i j ⊤
    fread : ∀ {i : I} → ProjF I Open → M i i (Maybe Char)
    fclose : ∀ {i j : I} →  ProjF I Open → InjF I Closed I → M i j ⊤
    throw : ∀ {i j : I} {A : Set} →  M i j ⊥


M : State → State → Set → Set
M i j A =
  Σ[ s ∈ State ] (i ≡ s) ×
  Σ[ s' ∈ State ] (j ≡ s') ×
  A



-- open PMonad public 
pmonadState : PMonad {State} {M}
pmonadState .PMonad.pure {i} x = i , refl , i , refl , x
(pmonadState PMonad.>>= m) f = {!   !}
-- (pmonadState >>= x) x₁ = x₁ x
-- -- (pmonadState >>= m) f = f m


-- open Combined public
-- combinedState : Combined
-- combinedState .pmonad = pmonadState
-- combinedState .look {i} {a} x = x i
-- combinedState .set x = tt
-- combinedState .fopen pf If = tt
-- combinedState .fread {i} x = nothing
-- combinedState .fclose = λ _ _ → tt
-- combinedState .throw = _





