module IndexedMonad.Exception where
open import Data.Unit    using (⊤; tt)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.Char using (Char)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Function using (_∘_)
open import Data.Empty using (⊥)

open import Data.String  using (String)
open import IndexedMonad.Definition


data State : Set where
  i  : State
  j : State


X : Set
X = String

EXP : Pred State → Pred State
EXP = ((X := i) :>>: (⊥ := i)) :+: --throw
      (( ⊤ := i) :>>: (X := i)) --handle


pattern FThrow x k = Do(InL( V x :& k))
pattern FHandle k = Do(InR( V tt :& k))

throw : X →  :∗ EXP (⊥ := i) i
throw x = FThrow x Ret

handle : :∗ EXP (X := i) i
handle = FHandle Ret