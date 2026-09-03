module McBride where


open import Data.Unit using (⊤; tt)
open import Data.Char using (Char)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.String using (String)

Pred : Set → Set₁
Pred I = I → Set

data State : Set where
  Open : State
  Closed : State

data SState : State → Set where
  sOpen : SState Open
  sClosed : SState Closed

infixr 0 _:→_
infixr 4 _:+:_

_:→_ : {I : Set} → Pred I → Pred I → Set
s :→ t = ∀ {i} → s i → t i

-- := pronounced 'at key'
data _:=_ {I : Set} (A : Set) (k : I) : I → Set where
  V : A → (A := k) k


record IFunctor {I O : Set} (F : Pred I → Pred O) : Set₁ where
  field
    imap : ∀ {s t} → (s :→ t) → (F s :→ F t)

record IMonad {I : Set} (M : Pred I → Pred I) : Set₁ where
  field
    imap : ∀ {s t} → (s :→ t) → (M s :→ M t)
    iskip : ∀ {p} → p :→ M p
    iextend : ∀ {p q} → (p :→ M q) → (M p :→ M q)

-- Binær
data _:>>:_ {I : Set} (P Q : Pred I) (R : Pred I) : Pred I where
  _:&_ : ∀ {i} → P i → (Q :→ R) → (P :>>: Q) R i


-- Sum
data _:+:_ {I : Set} (F G : Pred I → Pred I) (P : Pred I) : Pred I where
  InL : ∀ {i} → F P i → (F :+: G) P i
  InR : ∀ {i} → G P i → (F :+: G) P i

FilePath : Set
FilePath = String

FH : Pred State → Pred State
FH = ((FilePath := Closed) :>>: SState)
  :+: (((⊤ := Open) :>>: ((Maybe Char) := Open))
  :+: ((⊤ := Open) :>>: (⊤ := Closed)))


-- Free Monad
{-# NO_POSITIVITY_CHECK #-}
data _:*_ {I : Set} (F : Pred I → Pred I)(P : Pred I) : Pred I where
  Ret : ∀ {i} → P i → (F :* P) i
  Do : ∀ {i} → F (F :* P) i → (F :* P) i



pattern FOpen p k = Do (InL (V p :& k))
pattern FGetC k = Do (InR (InL (V tt :& k)))
pattern FClose k = Do (InR (InR (V tt :& k)))


fOpen : FilePath → (FH :* SState) Closed
fOpen p = FOpen p Ret

fGetC : (FH :* ((Maybe Char) := Open)) Open
fGetC = FGetC Ret

fClose : (FH :* (⊤ := Closed)) Open
fClose = FClose Ret


data LSState : Set where
  s : LSState

LS : Pred LSState → Pred LSState
LS = ((⊤ := s) :>>: (String := s))
     :+: ((String := s) :>>: (⊤ := s))

pattern PLook k = Do (InL (V tt :& k))
pattern PSet x k = Do (InR (V x :& k))


look : (LS :* (String := s)) s
look = PLook Ret

set : String → (LS :* (⊤ := s)) s
set x = PSet x Ret

