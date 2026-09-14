module Pmonad where
open import Data.Unit    using (⊤; tt)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.Char using (Char)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Function using (_∘_)
open import Data.String  using (String; uncons)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁)

data OC : Set where
  Open : OC
  Closed : OC

data SOC : OC → Set where
  SOpen : SOC Open
  SClosed : SOC Closed

State : Set
State = ℕ × OC


FH : Set
FH = String

record PMonad {I : Set} {M : I → I → Set → Set} : Set₁ where
  field
    pure : ∀ {i} {A : Set} → A → M i i A
    _>>=_ : ∀ {i j k} {A B : Set} → M i j A → (A → M j k B) → M i k B


ProjL : Set → Set → Set
ProjL I A = I → A

ProjF : Set → Set
ProjF I = I → OC

InjL : Set → Set → Set → Set
InjL I A J = I → A → J

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
    fclose : ∀ {i : I} → (getOC : ProjF I) → getOC i ≡ Open  → (inj : InjF I Closed I) → M i (inj i SClosed) ⊤
    throw : ∀ {i j : I} {A : Set} →  M i j ⊥


M : State → State → Set → Set
M i j A =
  (s : State) →
  s ≡ i →
  Σ[ s' ∈ State ] (s' ≡ j) × Maybe A

open PMonad
pmonadState : PMonad {State} {M}
pmonadState .pure a s ref = s , (ref , just a)
pmonadState ._>>=_ ma f s ref with ma s ref
... | x , fst , just x₁ = f x₁ x fst
... | x , fst , nothing = _ , refl , nothing


-- open Combined
combinedState : Combined {State} {M}
combinedState .Combined.pmonad = pmonadState
combinedState .Combined.look proj s ref = s , ref , just (proj s)
combinedState .Combined.set inj val s ref = inj s val , cong (λ x → inj x val) ref , just tt
combinedState .Combined.fopen getOC x inj fh s ref = (inj s SOpen) , cong (λ x₁ → inj x₁ SOpen) ref , just fh
combinedState .Combined.fread {i} getOC ref fh s x₂ with uncons fh
... | just (c , fp′) = s , x₂ , just (just c)
... | nothing = s , x₂ , nothing
combinedState .Combined.fclose {i} getOC ref inj s x₁ = inj s SClosed , (cong (λ x → inj x SClosed) x₁ , just tt)
combinedState .Combined.throw s x = _ , refl , nothing


infixr 1 _>>>=_
_>>>=_ = pmonadState .PMonad._>>=_


getMem : ProjL State ℕ
getMem (n , _) = n

getOC : ProjF State
getOC (_ , oc) = oc

setMem : InjL State ℕ State
setMem (n , oc) val = val , oc

openFile : InjF State Open State
openFile (n , _) o = n , Open

closeFile : InjF State Closed State
closeFile (n , _) _ = n , Closed


open Combined combinedState

myLook : ∀ {i : State} → M i i ℕ
myLook = look getMem

mySet : ∀ {i : State} → (val : ℕ) → M i (setMem i val) ⊤
mySet val = set setMem val

myFopen : ∀ {n : ℕ} → String → M (n , Closed) (n , Open) FH
myFopen fh = fopen getOC refl openFile fh

myFclose : ∀ {n : ℕ} → M (n , Open) (n , Closed) ⊤
myFclose = fclose getOC refl closeFile


--ReadOpenSetClose : ∀ {i : State} → M i (67 , Closed) ⊤
--ReadOpenSetClose (n , Open) refl = (67 , Closed) , refl , nothing
--ReadOpenSetClose (n , Closed) refl =
--  ((look getMem) >>>= λ val →
--  (fopen getOC refl openFile "Hello World") >>>= (λ fh →
--  (set setMem 67) >>>= λ z →
--  fclose getOC refl closeFile)) (n , Closed) refl


ReadOpenSetClose : ∀ {i : State} → M i (67 , Closed) ⊤
ReadOpenSetClose (n , Open) refl = (67 , Closed) , refl , nothing
ReadOpenSetClose (n , Closed) refl =
  (myLook >>>= λ val →
  (myFopen "Hello World") >>>= λ fp →
  (mySet 67) >>>= λ z → myFclose) (n , Closed) refl

testSuccess : Σ[ s' ∈ State ] (s' ≡ (67 , Closed)) × Maybe ⊤
testSuccess = ReadOpenSetClose (0 , Closed) refl

testFail : Σ[ s' ∈ State ] (s' ≡ (67 , Closed)) × Maybe ⊤
testFail = ReadOpenSetClose (0 , Open) refl

