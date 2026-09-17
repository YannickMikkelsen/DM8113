module Pmonad.Pmonad1 where
open import Data.Unit    using (⊤; tt)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.Char using (Char)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Function using (_∘_)
open import Data.String  using (String; uncons; _++_; fromChar)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁)

-- infixr 1 _>>>=_

data OC : Set where
  Open : OC
  Closed : OC

data SOC : OC → Set where
  SOpen : SOC Open
  SClosed : SOC Closed


data Flag : Set where
  OK        : Flag
  Unhandled : Flag

  
State : Set₁
State = Set × OC × Flag


FH : Set
FH = String

record PMonad {I : Set₁} {M : I → I → Set → Set₁} : Set₂ where
  field
    pure : ∀ {i} {A : Set} → A → M i i A
    _>>=_ : ∀ {i j k} {A B : Set} → M i j A → (A → M j k B) → M i k B


-- Get memory
ProjL : Set₁ → Set → Set₁ 
ProjL I A = I → A

-- Get FileStatus
ProjF : Set₁ → Set₁
ProjF I = I → OC

-- Set Memory
InjL : Set₁ → Set → Set₁ → Set₁
InjL I A J = I → A → J

-- Set File Status
InjF : Set₁ → OC → Set₁ → Set₁
InjF I S J = I → SOC S → J


record Combined {I : Set₁} {M : I → I → Set → Set₁} : Set₂ where
  field
    pmonad : PMonad {I} {M}
  field
    look : ∀ {i : I} {a : Set} → (proj : ProjL I a) → M i i a
    set  : ∀ {i : I} {a : Set} (inj : InjL I a I) (val : a) → M i (inj i val) ⊤
    fopen : ∀ {i : I} → (getOC : ProjF I) → getOC i ≡ Closed → (inj : InjF I Open I) → String →  M i (inj i SOpen) FH
    fread : ∀ {i : I} → (getOC : ProjF I) → getOC i ≡ Open → FH → M i i (Maybe Char)
    fwrite : ∀ {i : I} → (getOC : ProjF I) → getOC i ≡ Open → FH → Char → M i i FH
    fclose : ∀ {i : I} → (getOC : ProjF I) → getOC i ≡ Open  → (inj : InjF I Closed I) → M i (inj i SClosed) ⊤
    throw : ∀ {i : I} {A : Set} (inj : InjL I Flag I) → M i (inj i Unhandled) A
    catch : ∀ {i j : I} {A : Set} → M i j A → (resetFlag : InjL I Flag I) → (∀ {k : I} → M k j A) → M i j A


M : State → State → Set → Set₁
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
combinedState .Combined.throw setFlag s eq = setFlag s Unhandled , cong (λ x → setFlag x Unhandled) eq , nothing
combinedState .Combined.catch ma resetFlag mb s eq with ma s eq
... | s' , eq' , just x = s' , eq' , just x
... | s' , eq' , nothing = mb (resetFlag s' OK) (cong (λ st → resetFlag st OK) eq')




_>>>=_ : ∀ {i j k} {A B : Set} → M i j A → (A → M j k B) → M i k B
_>>>=_ = PMonad._>>=_ pmonadState


getMem : ProjL State ℕ
getMem (_ , _ , _) = 0

setMem : InjL State ℕ State
setMem (_ , oc , flag) val = (ℕ , oc , flag)

getStatus : ProjF State
getStatus (_ , oc , _) = oc

setOpen : InjF State Open State
setOpen (a , _ , flag) _ = (a , Open , flag)

setClosed : InjF State Closed State
setClosed (a , _ , flag) _ = (a , Closed , flag)



open Combined combinedState

readMem : ∀ {i : State} → M i i ℕ
readMem = look getMem

writeMem : ∀ {i : State} → (val : ℕ) → M i (setMem i val) ⊤
writeMem val = set setMem val

openFile : ∀ {n : Set} → String → M (n , Closed , OK) (n , Open , OK) FH
openFile fh = fopen getStatus refl setOpen fh

closeFile : ∀ {n : Set} → M (n , Open , OK) (n , Closed , OK) ⊤
closeFile = fclose getStatus refl setClosed

readFile : ∀ {n : Set} → FH → M (n , Open , OK) (n , Open , OK) (Maybe Char)
readFile fh = fread getStatus refl fh

writeFile : ∀ {n : Set} → FH → Char → M (n , Open , OK) (n , Open , OK) FH
writeFile fh c = fwrite getStatus refl fh c



-----------------SKLA KIGGES PÅ-------
setMemFH : InjL State ⊤ State
setMemFH (_ , oc , flag) _ = (FH , oc , flag)

setOK : InjL State ⊤ State
setOK (mem , oc , _) _ = (mem , oc , OK)

finishFromOpen : ∀ {n : Set} → M (n , Open , OK) (FH , Closed , OK) ⊤
finishFromOpen {n} =
  readFile {n} "" >>>= λ _ →
  closeFile {n}   >>>= λ _ →
  set setMemFH tt

ReadOpenSetClose : ∀ {i : State} → M i (FH , Closed , OK ) ⊤
ReadOpenSetClose (fst , Open , OK) x =
  finishFromOpen {fst} (fst , Open , OK) refl
ReadOpenSetClose (fst , Closed , OK) x =
  (openFile {fst} "" >>>= λ fh → finishFromOpen {fst})
    (fst , Closed , OK) refl
ReadOpenSetClose (fst , Open , Unhandled) x =
  (set setOK tt >>>= λ _ → finishFromOpen {fst})
    (fst , Open , Unhandled) refl
ReadOpenSetClose (fst , Closed , Unhandled) x =
  (set setOK tt >>>= λ _ → openFile {fst} "" >>>= λ fh → finishFromOpen {fst})
    (fst , Closed , Unhandled) refl