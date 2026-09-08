module McBride where


open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
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
infixl 4 _>>=_
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
    imap : ∀ {s t} → (s :→ t) → (M s :→ M t) -- Functor Map
    iskip : ∀ {p} → p :→ M p -- Return/Pure
    iextend : ∀ {p q} → (p :→ M q) → (M p :→ M q) -- Bind

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

-- Look/Set Class

data LSState : Set where
  s : LSState

LS : (I : Set) → Pred I → Pred I
LS I P i = (((⊤ := i) :>>: (String := i))
     :+: ((String := i) :>>: (⊤ := i))) P i

pattern PLook k = Do (InL (V tt :& k))
pattern PSet x k = Do (InR (V x :& k))


look : ∀ {I : Set} {i : I} → (LS I :* (String := i)) i
look = PLook Ret

set : ∀ {I : Set} {i : I} → String → (LS I :* (⊤ := i)) i
set x = PSet x Ret

-- Exception Class

EXC : (I : Set) → Set → Pred I → Pred I
EXC I E P i = (((E := i) :>>: (⊥ := i)) :+: ((⊤ := i) :>>: (E := i))) P i

pattern PThrow e k = Do (InL (V e :& k))
pattern PHandle k = Do (InR (V tt :& k))

throw : ∀ {I E : Set} {i : I} → E → (EXC I E :* (⊥ := i)) i
throw e = PThrow e Ret

handle : ∀ {I E : Set} {i : I} → (EXC I E :* (E := i)) i
handle = PHandle Ret


-- Kombination af effekterne

CombinedOld : (S E : Set) → Pred S → Pred S
CombinedOld S E = LS S :+: (EXC S E)

Combined : Set → Pred State → Pred State
Combined E = FH :+: (LS State :+: EXC State E)

-- IFunctor

IFunctor:>>: : ∀ {I : Set} {P Q : Pred I} → IFunctor ((P :>>: Q))
IFunctor:>>: .IFunctor.imap f (p :& k) = p :& λ q → f (k q)

IFunctor:+: : ∀ {I : Set} {F G : Pred I → Pred I} → IFunctor F → IFunctor G → IFunctor (F :+: G)
IFunctor:+: iF iG .IFunctor.imap f (InL x) = InL (IFunctor.imap iF f x)
IFunctor:+: iF iG .IFunctor.imap f (InR y) = InR (IFunctor.imap iG f y)



IFunctorLS : ∀ {I : Set} → IFunctor (LS I)
IFunctorLS .IFunctor.imap f (InL x) = InL (IFunctor.imap IFunctor:>>: f x)
IFunctorLS .IFunctor.imap f (InR y) = InR (IFunctor.imap IFunctor:>>: f y)

IFunctorEXC : ∀ {I E : Set} → IFunctor (EXC I E)
IFunctorEXC .IFunctor.imap f (InL x) = InL (IFunctor.imap IFunctor:>>: f x)
IFunctorEXC .IFunctor.imap f (InR y) = InR (IFunctor.imap IFunctor:>>: f y)

IFunctorFH : IFunctor FH
IFunctorFH = IFunctor:+: IFunctor:>>: (IFunctor:+: IFunctor:>>: IFunctor:>>:)

instance
  IFunctorCombinedOld : ∀ {S E : Set} → IFunctor (CombinedOld S E)
  IFunctorCombinedOld .IFunctor.imap f (InL x) = InL (IFunctor.imap IFunctorLS f x)
  IFunctorCombinedOld .IFunctor.imap f (InR y) = InR (IFunctor.imap IFunctorEXC f y)

instance
  IFunctorCombined : ∀ {E : Set} → IFunctor (Combined E)
  IFunctorCombined = IFunctor:+: IFunctorFH (IFunctor:+: IFunctorLS IFunctorEXC)

{-# TERMINATING #-}
mapM : ∀ {I : Set} {F : Pred I → Pred I} → IFunctor F → ∀ {p q} → (p :→ q) → ((F :* p) :→ (F :* q))
mapM iF f (Ret x) = Ret (f x)
mapM iF f (Do x)  = Do (IFunctor.imap iF (mapM iF f) x)

{-# TERMINATING #-}
bindM : ∀ {I : Set} {F : Pred I → Pred I} → IFunctor F → ∀ {p q} → (p :→ (F :* q)) → ((F :* p) :→ (F :* q))
bindM iF f (Ret x) = f x
bindM iF f (Do x)  = Do (IFunctor.imap iF (bindM iF f) x)


FreeIMonad : ∀ {I : Set} {F : Pred I → Pred I} → IFunctor F → IMonad (F :*_)
FreeIMonad iF .IMonad.imap = mapM iF
FreeIMonad iF .IMonad.iskip = Ret
FreeIMonad iF .IMonad.iextend = bindM iF


_>>=_ : ∀ {I : Set} {F : Pred I → Pred I} {p q : Pred I} {i : I} → {{iF : IFunctor F}} → (F :* p) i → (p :→ (F :* q)) → (F :* q) i

_>>=_ {{iF = iF}} m f = IMonad.iextend (FreeIMonad iF) f m

CombinedIMonad : ∀ {S E : Set} → IMonad ((Combined E) :*_)
CombinedIMonad = FreeIMonad IFunctorCombined


-- Constructors

-- Look/Set
lookC : ∀ {E : Set} {s : State} → ((Combined E) :* (String := s)) s
lookC = Do (InR (InL (InL ((V tt) :& Ret))))

setC : ∀ {E : Set} {s : State} → String → ((Combined E) :* (⊤ := s)) s
setC x = Do (InR (InL (InR ((V x) :& Ret))))

-- Expections
throwC : ∀ {E : Set} {s : State} → E → ((Combined E) :* (⊥ := s)) s
throwC e = Do (InR (InR (InL ((V e) :& Ret))))

handleC : ∀ {E : Set} {s : State} → ((Combined E) :* (E := s)) s
handleC = Do (InR (InR (InR ((V tt) :& Ret))))

-- FileHandling

openC : ∀ {E : Set} → FilePath → ((Combined E) :* SState) Closed
openC p = Do (InL (InL ((V p) :& Ret)))

getC : ∀ {E : Set} → ((Combined E) :* ((Maybe Char) := Open)) Open
getC = Do (InL (InR (InL ((V tt) :& Ret))))

closeC : ∀ {E : Set} → ((Combined E) :* (⊤ := Closed)) Open
closeC = Do (InL (InR (InR ((V tt) :& Ret))))



-- Test

exampleProgram : ∀ {s : State} → ((Combined String) :* (⊤ := s)) s
exampleProgram = lookC >>= λ { (V str) → setC "Ny tilstand"
                       >>= λ { (V tt) → Ret (V tt)}}


exampleProgramWithException : ∀ {s : State} → ((Combined String) :* (⊤ := s)) s
exampleProgramWithException = lookC >>= λ { (V str) → setC "Ny tilstand"
                                    >>= λ { (V tt) → throwC "Fejl opstået"
                                    >>= λ { (V ())}}}



-- Interpreter

data Res {E : Set} (A : Pred State) (s : State) : Set where
  Succes : ∀ {i} → A i → String → Res {E} A s
  Error : E → Res {E} A s

runStep : ∀ {E : Set} {A : Pred State} {s1 s2 : State} → Res {E} A s2 → Res {E} A s1
runStep (Succes x st) = Succes x st
runStep (Error e) = Error e


{-# TERMINATING #-}
run : ∀ {E : Set} {A : Pred State} {i : State} → String → ((Combined E) :* A) i → Res {E} A i
run st (Ret x) = Succes x st -- Pure/Return

run st (Do (InL (InL (V p :& k)))) = runStep (run st (k sOpen))  -- Open
run st (Do (InL (InR (InL (V tt :& k))))) = run st (k (V (just 'a'))) -- getC
run st (Do (InL (InR (InR (V tt :& k))))) = runStep (run st (k (V tt))) -- Close

run st (Do (InR (InL (InL (V tt :& k))))) = run st (k (V st)) -- Look
run st (Do (InR (InL (InR (V x :& k))))) = run x (k (V tt)) -- Set


run st (Do (InR (InR (InL (V e :& k))))) = Error e -- Throw
run st (Do (InR (InR (InR (V tt :& k))))) = run st (k (V {!!})) -- Handle
