module IndexedMonad.LS where
open import Data.Unit    using (⊤; tt)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.Char using (Char)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Function using (_∘_)

open import Data.String  using (String)
open import IndexedMonad.Definition


data State : Set where
  s   : State

-- data SState : State → Set where
--   sOpen   : SState Open
--   sClosed : SState Closed

Val : Set
Val = String

LS : Pred State → Pred State
LS = ((⊤ := s) :>>: (Val := s)) :+: --look
 ((Val := s) :>>: (⊤ := s)) --set


-- LS-IFunctor : IFunctor LS
-- LS-IFunctor .imap x (InL x₁) = InL (x₁ .pi :& (λ {i = i₁} z → x (x₁ .k z)))
-- LS-IFunctor .imap x (InR x₁) = InR (x₁ .pi :& (λ {i = i₁} z → x (x₁ .k z)))

pattern FLook k = Do(InL( V tt :& k))
pattern FSet p k = Do(InR( V p :& k))

look : :∗ LS (Val := s) s
look = FLook Ret

set : Val → :∗ LS (⊤ := s) s
set p = FSet p Ret




-- record LookSetTheory {I : Set} (M : Pred I → Pred I) (s : I) (Val : Set) : Set₁ where
--   field
--     isMonad : IMonad M

--   open IMonad isMonad public

--   field
--     look' : M (Val := s) s
--     set'  : Val → M (⊤ := s) s

--     law-read-skip
--       : ∀ {Q : Pred I} (v : M Q s)
--       → iextend isMonad {!   !} look' ≡ v

--     law-read-write-same
--       : ∀ {Q : Pred I} (k : Val → M Q s)
--       → {!   !}

--     law-read-read
--       : ∀ {Q : Pred I} (k : Val → Val → M Q s)
--       → {!   !}

--     law-write-read
--       : ∀ {Q : Pred I} (k : Val → M Q s) (y : Val)
--       → {!   !}
