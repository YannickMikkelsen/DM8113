module IndexedMonad.program where
open import Data.Unit    using (⊤; tt)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.Char using (Char)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Function using (_∘_)
open import Data.Empty using (⊥)
open import Data.Nat using (_+_)

open import Data.String  using (String)
open import IndexedMonad.Definition


data State : Set where
  s   : State
  i   : State

Val : Set
Val = ℕ

X : Set
X = ℕ

LS : Pred State → Pred State
LS = ((⊤ := s) :>>: (Val := s)) :+: --look
 ((Val := s) :>>: (⊤ := s)) --set


EXP : Pred State → Pred State
EXP = ((X := i) :>>: (⊥ := i)) :+: --throw
      (( ⊤ := i) :>>: (X := i)) --handle

PRO : Pred State → Pred State
PRO = LS :+: EXP

pattern FLook k = Do(InL(InL( V tt :& k)))
pattern FSet p k = Do(InL(InR( V p :& k)))

pattern FThrow x k = Do(InR(InL( V x :& k)))
pattern FHandle k = Do(InR(InR( V tt :& k)))



look : :∗ PRO (Val := s) s
look = FLook Ret

set : Val → :∗ PRO (⊤ := s) s
set p = FSet p Ret

throw : X →  :∗ PRO (⊥ := i) i
throw x = FThrow x (λ { (V ()) })

handle : :∗ PRO (X := i) i
handle = FHandle Ret


PRO-IFunctor : IFunctor PRO
PRO-IFunctor .imap x (InL (InL (pi₁ :& k₁))) = InL (InL (pi₁ :& (λ {i = i₂} z → x (k₁ z))))
PRO-IFunctor .imap x (InL (InR (pi₁ :& k₁))) = InL (InR (pi₁ :& (λ {i = i₂} z → x (k₁ z))))
PRO-IFunctor .imap x (InR (InL x₁)) = InR (InL (x₁ .pi :& (λ {i = i₂} z → x (x₁ .k z))))
PRO-IFunctor .imap x (InR (InR x₁)) = InR (InR (x₁ .pi :& (λ {i = i₂} z → x (x₁ .k z))))

PRO-IMonad : IMonad (:∗ PRO)
PRO-IMonad .iskip = Ret
PRO-IMonad .iextend x (Ret x₁) = x x₁
PRO-IMonad .iextend x (FLook k₁) = FLook (λ z → PRO-IMonad .iextend x (k₁ z))
PRO-IMonad .iextend x (FSet x₁ k₁) = FSet x₁ ((λ z → PRO-IMonad .iextend x (k₁ z)))
PRO-IMonad .iextend x (FThrow x₁ k₁) = FThrow x₁ ((λ z → PRO-IMonad .iextend x (k₁ z)))
PRO-IMonad .iextend x (FHandle k₁) = FHandle ((λ z → PRO-IMonad .iextend x (k₁ z)))


_»=_ : ∀ {P Q : Pred State} {st} → :∗ PRO P st → (P :→ :∗ PRO Q) → :∗ PRO Q st
m »= f = PRO-IMonad .iextend f m
infixl 1 _»=_


incr : :∗ PRO (⊤ := s) s
incr = look »= λ { (V v) → set (v + 1) }



