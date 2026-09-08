module IndexedMonad.newstatetest where
open import Data.Unit    using (⊤; tt)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.Char using (Char)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Function using (_∘_)
open import Data.Empty using (⊥)
open import Data.Nat using (_+_)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Data.String  using (String)
open import IndexedMonad.Definition


data FileState : Set where
  Open   : FileState
  Closed : FileState

data MemState : Set where
  i : MemState

data SState : FileState → Set where
  sOpen   : SState Open
  sClosed : SState Closed

State : Set
State = FileState × MemState

Val : Set
Val = ℕ

X : Set
X = ℕ

FilePath : Set
FilePath = String

LS : Pred MemState → Pred MemState
LS = ((⊤ := i) :>>: (Val := i))     -- look
  :+: ((Val := i) :>>: (⊤ := i))    -- set

FH : Pred FileState → Pred FileState
FH = ((FilePath := Closed) :>>: SState)                    -- fOpen
  :+: (((⊤ := Open) :>>: (Maybe Char := Open))              -- fGetC
  :+:  ((⊤ := Open) :>>: (⊤ := Closed)))                    -- fClose

FH-lift : Pred State → Pred State
FH-lift Q (f , m) = FH (λ f′ → Q (f′ , m)) f

LS-lift : Pred State → Pred State
LS-lift Q (f , m) = LS (λ m′ → Q (f , m′)) m

PRO : Pred State → Pred State
PRO = FH-lift :+: LS-lift

pattern FOpen p k = Do(InL(InL( V p :& k)))
pattern FGetC k   = Do(InL(InR(InL( V tt :& k))))
pattern FClose k  = Do(InL(InR(InR( V tt :& k))))

pattern FLook k  = Do(InR(InL( V tt :& k)))
pattern FSet p k = Do(InR(InR( V p :& k)))


LiftF : Pred FileState → Pred State
LiftF P (f , m) = P f

Opened : MemState → Pred State
Opened m (f , m′) = SState f × m ≡ m′

look : ∀ {f} → :∗ PRO (Val := (f , i)) (f , i)
look {f} = FLook (λ { (V v) → Ret (V v) })

set : Val → ∀ {f} → :∗ PRO (⊤ := (f , i)) (f , i)
set p {f} = FSet p (λ { (V tt) → Ret (V tt) })

fOpen : FilePath → ∀ {m} → :∗ PRO (Opened m) (Closed , m)
fOpen x {m} = FOpen x (λ s → Ret (s , refl))

fGetC : ∀ {m} → :∗ PRO (Maybe Char := (Open , m)) (Open , m)
fGetC {m} = FGetC (λ { (V c) → Ret (V c) })

fClose : ∀ {m} → :∗ PRO (⊤ := (Closed , m)) (Open , m)
fClose {m} = FClose (λ { (V tt) → Ret (V tt) })



PRO-IFunctor : IFunctor PRO
PRO-IFunctor .imap x (InL (InL (pi₁ :& k₁))) = InL (InL (pi₁ :& (λ {i = i₂} z → x (k₁ z))))
PRO-IFunctor .imap x (InL (InR (InL x₁))) = InL (InR (InL (x₁ .pi :& (λ {i = i₂} z → x (x₁ .k z)))))
PRO-IFunctor .imap x (InL (InR (InR x₁))) = InL (InR (InR (x₁ .pi :& (λ {i = i₂} z → x (x₁ .k z)))))
PRO-IFunctor .imap x (InR (InL (pi₁ :& k₁))) = InR (InL (pi₁ :& (λ {i = i₂} z → x (k₁ z))))
PRO-IFunctor .imap x (InR (InR x₁)) = InR (InR (x₁ .pi :& (λ {i = i₂} z → x (x₁ .k z))))


PRO-IMonad : IMonad (:∗ PRO)
PRO-IMonad = instance3 PRO-IFunctor

open Bind PRO-IMonad


incr : ∀ {f} → :∗ PRO (⊤ := (f , i)) (f , i)
incr {f} = look =>= λ v → set (v + 1)


readFirstChar : ∀ {m} → FilePath → :∗ PRO (Maybe Char := (Closed , m)) (Closed , m)
readFirstChar {m} fp =
  (fOpen fp) ?>= λ { (sOpen  , refl) → fGetC =>= λ c → fClose =>= λ _ → Ret (V c)
                    ; (sClosed , refl) → Ret (V nothing) }


program : FilePath → Val → :∗ PRO (Maybe ℕ := (Closed , i)) (Closed , i)
program fp m = look =>= λ c → set (c + 1) 
                    =>= λ tt → (fOpen fp) 
                    ?>= (λ{(sOpen , refl) → (set (c + 5)) 
                                =>= (λ tt → fClose 
                                =>= (λ _ → look 
                                =>= λ v → Ret ((V (just v)))))
                                 ;
        (sClosed , refl) → look =>= (λ v → Ret (V (just v)))})