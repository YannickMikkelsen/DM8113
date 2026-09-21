module Pmonad.Pmonad where
open import Data.Unit    using (⊤; tt)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.Char using (Char)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Function using (_∘_)
open import Data.String  using (String; uncons; _++_; fromChar)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂)

infixr 1 _>>>=_

data OC : Set where
  Open : OC
  Closed : OC

data SOC : OC → Set where
  SOpen : SOC Open
  SClosed : SOC Closed


data Flag : Set where
  OK        : Flag
  Unhandled : Flag


State : Set
State = ℕ × OC × Flag
-- Set × OC x flag

FH : Set
FH = String

record PMonad {I : Set} {M : I → I → Set → Set} : Set₁ where
  field
    pure : ∀ {i} {A : Set} → A → M i i A
    _>>=_ : ∀ {i j k} {A B : Set} → M i j A → (A → M j k B) → M i k B

-- Get memory
ProjL : Set → Set → Set
ProjL I A = I → A

-- Get FileStatus
ProjF : Set → Set
ProjF I = I → OC

-- Set Memory
InjL : Set → Set → Set → Set
InjL I A J = I → A → J

-- Set File Status
InjF : Set → OC → Set → Set
InjF I S J = I → SOC S → J



record Combined {I : Set} {M : I → I → Set → Set} : Set₁ where
  field
    pmonad : PMonad {I} {M}
  field
    look : ∀ {i : I} {a : Set} → (proj : ProjL I a) → M i i a
    set  : ∀ {i : I} {a : Set} (inj : InjL I a I) (val : a) → M i (inj i val) ⊤
    fopen : ∀ {i : I} → (getOC : ProjF I) → getOC i ≡ Closed → (inj : InjF I Open I) → String →  M i (inj i SOpen) FH
    fread : ∀ {i : I} → (getOC : ProjF I) → getOC i ≡ Open → FH → M i i (Maybe Char)
    fwrite : ∀ {i : I} → (getOC : ProjF I) → getOC i ≡ Open → FH → Char → M i i FH
    fclose : ∀ {i : I} → (getOC : ProjF I) → getOC i ≡ Open  → (inj : InjF I Closed I) → M i (inj i SClosed) ⊤
    throw : ∀ {i j : I} {A : Set} →  M i j A -- M i i A
    catch : ∀ {i j : I} {A : Set} → M i j A → (∀ {k : I} → M k j A) → M i j A


M : State → State → Set → Set
-- M i j A = (s : State) → s ≡ i → Maybe (Σ[ s' ∈ State ] (s' ≡ j) × A)
M i j A = (s : State) → s ≡ i → Σ[ s' ∈ State ] (s' ≡ j) × Maybe A

open PMonad

pmonadState : PMonad {State} {M}
pmonadState .pure x s eq = s , (eq , just x)
pmonadState ._>>=_ ma f s eq with ma s eq
... | st' , stEq , just res = f res st' stEq
... | st' , stEq , nothing = _ , refl , nothing

combinedState : Combined {State} {M}
combinedState .Combined.pmonad = pmonadState
combinedState .Combined.look getMem s eq = s , eq , just (getMem s)
combinedState .Combined.set setMem val s eq = setMem s val , cong (λ st → setMem st val) eq , just tt
combinedState .Combined.fopen getOC _ setStatus fh s eq = (setStatus s SOpen) , cong (λ st → setStatus st SOpen) eq , just fh
combinedState .Combined.fread getOC _ fh s eq with uncons fh
... | just (c , _) = s , eq , just (just c)
... | nothing = s , eq , just (nothing)
combinedState .Combined.fwrite getOC _ fh c s eq = s , (eq , (just (fh ++ fromChar c)))
combinedState .Combined.fclose getOC _ setStatus s eq = setStatus s SClosed , (cong (λ st → setStatus st SClosed) eq , just tt)
combinedState .Combined.throw s eq = _ , refl , nothing
combinedState .Combined.catch ma mb s eq with ma s eq
... | s' , eq' , just x = s' , eq' , just x
... | s' , eq' , nothing = mb s' eq'


_>>>=_ = pmonadState .PMonad._>>=_

getMem : ProjL State ℕ
getMem (n , _ , _) = n

getOC : ProjF State
getOC (_ , oc , _) = oc

setMem : InjL State ℕ State
setMem (n , oc , fl) val = val , oc , fl

openFileStatus : InjF State Open State
openFileStatus (n , _ , fl) o = n , Open , fl

closeFileStatus : InjF State Closed State
closeFileStatus (n , _ , fl) _ = n , Closed , fl

open Combined combinedState

readMem : ∀ {i : State} → M i i ℕ
readMem = look getMem

writeMem : ∀ {i : State} → (val : ℕ) → M i (setMem i val) ⊤
writeMem val = set setMem val

openFile : ∀ {n : ℕ}{fl : Flag} → String → M (n , Closed , fl) (n , Open , fl) FH
openFile fh = fopen getOC refl openFileStatus fh

closeFile : ∀ {n : ℕ}{fl : Flag} → M (n , Open , fl) (n , Closed , fl) ⊤
closeFile = fclose getOC refl closeFileStatus

readFile : ∀ {n : ℕ}{fl : Flag} → FH → M (n , Open , fl) (n , Open , fl) (Maybe Char)
readFile fh = fread getOC refl fh

writeFile : ∀ {n : ℕ}{fl : Flag} → FH → Char → M (n , Open , fl) (n , Open , fl) FH
writeFile fh c = fwrite getOC refl fh c



ReadOpenSetClose : ∀ {i : State} → M i (67 , Closed , proj₂ (proj₂ i)) ⊤
ReadOpenSetClose (n , Open , fl) refl = (67 , Closed , fl) , refl , nothing
ReadOpenSetClose (n , Closed , fl) refl =
  ((readMem) >>>= λ val →
  (openFile "Hello World") >>>= (λ fh →
  (writeMem 67) >>>= λ z →
  closeFile)) (n , Closed , fl) refl

ReadCharAndUpdate : ∀ {i : State} → String → M i (67 , Closed , proj₂ (proj₂ i)) (Maybe Char)
ReadCharAndUpdate fh (n , Open , fl) refl = (67 , Closed , fl) , refl , nothing
ReadCharAndUpdate fh (n , Closed , fl) refl =
  (openFile fh >>>= λ handle →
  readFile handle >>>= λ charOpt →
  writeMem 67 >>>= λ _ →
  closeFile >>>= λ _ → pmonadState .pure charOpt ) (n , Closed , fl) refl

OpenWriteThrow : ∀ {i : State} → String → M i (67 , Closed , Unhandled) ⊤
OpenWriteThrow fh (n , Open , fl) refl = throw (n , Open , fl) refl
OpenWriteThrow fh (n , Closed , fl) refl =
  ((openFile fh) >>>= ( λ handle →
  (writeFile handle 'A') >>>= λ _ →
  throw)) (n , Closed , fl) refl

BadProgram : ∀ {i : State} → M i (0 , Closed , proj₂ (proj₂ i)) ⊤
BadProgram {n , Open , fl} s eq = throw s eq
BadProgram {n , Closed , fl} s eq =
  (openFile "File.txt" >>>= λ x →
  writeMem 132435678 >>>= λ _ →
  throw) s eq

testOpenWriteThrow : Σ[ s' ∈ State ] (s' ≡ (67 , Closed , Unhandled)) × Maybe ⊤
testOpenWriteThrow = OpenWriteThrow "A" (0 , Closed , OK) refl

testReadChar : Σ[ s' ∈ State ] (s' ≡ (67 , Closed , OK)) × Maybe (Maybe Char)
testReadChar = ReadCharAndUpdate "Hello World" (0 , Closed , OK) refl

testSuccess : Σ[ s' ∈ State ] (s' ≡ (67 , Closed , OK)) × Maybe ⊤
testSuccess = ReadOpenSetClose (0 , Closed , OK) refl

testFail : Σ[ s' ∈ State ] (s' ≡ (67 , Closed , OK)) × Maybe ⊤
testFail = ReadOpenSetClose (0 , Open , OK) refl




-- failAfterWrite : ∀ {n : ℕ} → M (n , Closed) (99 , Closed) ⊤
-- failAfterWrite {n} (n , Closed) refl =
--   ((writeMem 99) >>>= (λ _ →
--   throw)) (99 , Closed) refl

-- recoverMem : ∀ {k : State} → M k (99 , Closed) ⊤
-- recoverMem {k} (fst , Open) eq = pure ? ?
-- recoverMem {k} (fst , Closed) eq = ?

-- testMemCollision : M (0 , Closed) (99 , Closed) ⊤
-- testMemCollision = catch failAfterWrite recoverMem

