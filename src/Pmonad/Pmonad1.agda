module Pmonad.Pmonad1 where
open import Agda.Primitive using (Setω)
open import Level using (Level; suc; zero; _⊔_)
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
open import Data.Sum using (_⊎_; inj₁; inj₂)


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
-- vi har flag for at indikerer at der er skat en fejl og dermed at resultatet ikke kan bruges 
-- catch throw1 :: catch (throw e) h ≡ h e
-- catch throw2 :: catch t throw ≡ t
-- Bad idea!

FH : Set
FH = String

record PMonad {I : Set₁} {M : ∀ {l} → I → I → Set l → Set (suc zero ⊔ l)} : Setω  where
  field
    pure : ∀ {l} {i} {A : Set l} → A → M i i A
    _>>=_ : ∀ {l₁ l₂} {i j k} {A : Set l₁} {B : Set l₂} → M i j A → (A → M j k B) → M i k B


-- Get memory
ProjL : ∀ {l} → Set₁ → Set l → Set (suc zero ⊔ l)
ProjL I A = I → A

-- Get FileStatus
ProjF : Set₁ → Set₁
ProjF I = I → OC

-- Set Memory
InjL : ∀ {l} → Set₁ → Set l → Set₁ → Set (suc zero ⊔ l)
InjL I A J = I → A → J

-- Set File Status
InjF : Set₁ → OC → Set₁ → Set₁
InjF I S J = I → SOC S → J

InjC : Set₁ → Set₁ → Set₁
InjC I J = I → J




record Combined {I : Set₁} {M : ∀ {l} → I → I → Set l → Set (suc zero ⊔ l)} : Setω  where
  field
    pmonad : PMonad {I} {M}
  field
    look : ∀ {i : I} {l} {a : Set l} → (proj : ProjL I a) → M i i a
    set  : ∀ {i : I} {l} {a : Set l} (inj : InjL I a I) (val : a) → M i (inj i val) ⊤
    fopen : ∀ {i : I} → (getOC : ProjF I) → getOC i ≡ Closed → (inj : InjF I Open I) → String →  M i (inj i SOpen) FH
    fread : ∀ {i : I} → (getOC : ProjF I) → getOC i ≡ Open → FH → M i i (Maybe Char)
    fwrite : ∀ {i : I} → (getOC : ProjF I) → getOC i ≡ Open → FH → Char → M i i FH
    fclose : ∀ {i : I} → (getOC : ProjF I) → getOC i ≡ Open  → (inj : InjF I Closed I) → M i (inj i SClosed) ⊤
    throw : ∀ {i : I} {l} {A : Set l} (inj : InjL I Flag I) → M i (inj i Unhandled) A
    catch : ∀ {i j : I} {l} {A : Set l} → M i j A → (failFlag  : InjC I I) → (resetFlag : InjC I I) → (∀ {k : I} → M k (failFlag j) A ⊎ M k (resetFlag j) A) → M i (failFlag j) A ⊎ M i (resetFlag j) A

M : ∀ {l} → State → State → Set l → Set (suc zero ⊔ l)
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
combinedState .Combined.catch {i} {j} x failFlag resetFlag h with x i refl
... | (fst , fst₂ , OK) , eq' , a = inj₂ (λ _ _ → (resetFlag (fst , fst₂ , OK)) , cong resetFlag eq' , a)
... | (fst , fst₂ , Unhandled) , eq' , a = h



_>>>=_ : ∀ {i j k} {A B : Set} → M i j A → (A → M j k B) → M i k B
_>>>=_ = PMonad._>>=_ pmonadState


getMem : ProjL State Set 
getMem (n , _ , _) = n

setMem : InjL State ℕ State
setMem (_ , oc , flag) val = (ℕ , oc , flag)

getStatus : ProjF State
getStatus (_ , oc , _) = oc

setOpen : InjF State Open State
setOpen (a , _ , flag) _ = (a , Open , flag)

setClosed : InjF State Closed State
setClosed (a , _ , flag) _ = (a , Closed , flag)



open Combined combinedState

readMem : ∀ {i : State} → M i i Set
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
ReadOpenSetClose (fst , Open , OK) x = finishFromOpen {fst} (fst , Open , OK) refl
ReadOpenSetClose (fst , Closed , OK) x = (openFile {fst} "" >>>= λ fh → finishFromOpen {fst}) (fst , Closed , OK) refl
ReadOpenSetClose (fst , Open , Unhandled) x = (set setOK tt >>>= λ _ → finishFromOpen {fst}) (fst , Open , Unhandled) refl
ReadOpenSetClose (fst , Closed , Unhandled) x = (set setOK tt >>>= λ _ → openFile {fst} "" >>>= λ fh → finishFromOpen {fst}) (fst , Closed , Unhandled) refl




setFlagOK : InjC State State 
setFlagOK (mem , oc , _) = (mem , oc , OK)

setFlagUN : InjC State State
setFlagUN (mem , oc , _) = (mem , oc , Unhandled)


setFlag : InjL State Flag State
setFlag (mem , oc , _) f = (mem , oc , f)



throwsAway : ∀ {n : Set} {oc : OC} → M (n , oc , OK) (n , oc , Unhandled) ⊤
throwsAway = throw setFlag





throwprogram : ∀ {n : Set} → M (n , Closed , OK) (n , Open , Unhandled) ⊤
throwprogram s x = ((openFile "hello.txt") >>>= λ fh → throw setFlag) s x


setFlagHandeler : InjL State Flag State
setFlagHandeler (mem , oc , _) f = (mem , Closed , f)


-- handler :  ∀ {n : Set} {oc : OC} {fl : Flag} → (M (n , oc , fl) (n , Closed , Unhandled) ⊤) ⊎ (M (n , oc , fl) (n , Closed , OK) ⊤)
-- handler {n} {Open} {OK} = inj₂ λ s x → closeFile s x
-- handler {n} {Closed} {OK} = inj₂ λ s z → s , z , just tt
-- handler {n} {Open} {Unhandled} = inj₁ (throw setFlagHandeler)
-- handler {n} {Closed} {Unhandled} = inj₂ (set setFlag OK) 


handler′ : ∀ {n : Set} {k : State}
         → M k (n , Closed , Unhandled) ⊤ ⊎ M k (n , Closed , OK) ⊤
handler′ {n} {fst , Open , OK} = inj₂ λ s z → (n , Closed , OK) , refl , just tt
handler′ {n} {fst , Closed , OK} = inj₂ λ s z → (n , Closed , OK) , refl , nothing
handler′ {n} {fst , Open , Unhandled} = inj₁ (λ _ _ → throw setFlagHandeler (n , Open , Unhandled) refl)
handler′ {n} {fst , Closed , Unhandled} = inj₂ λ s x → (n , Closed , OK) , refl , nothing


failFlag : InjC State State
failFlag (n , oc , fl) = (n , Closed , Unhandled)

resetFlag : InjC State State
resetFlag (n , oc , fl) = (n , Closed , OK)


catchExample : ∀ {n : Set} → (M (n , Closed , OK) (n , Closed , Unhandled) ⊤) ⊎ (M (n , Closed , OK) (n , Closed , OK) ⊤)
catchExample {n} = catch throwprogram failFlag resetFlag handler′


throwProgram′ :
  ∀ {n : Set} {oc : OC} {fl : Flag} →
  M (n , oc , fl) (n , Closed , Unhandled) ⊤
throwProgram′ {n} {oc} {fl} = throw setFlagHandeler

catchExample′ :
  ∀ {n : Set} {oc : OC} {fl : Flag} →
  M (n , oc , fl) (n , Closed , Unhandled) ⊤ ⊎
  M (n , oc , fl) (n , Closed , OK) ⊤
catchExample′ {n} {oc} {fl} =
  catch (throwProgram′ {n} {oc} {fl}) failFlag resetFlag handler′

-- Synes ikke flag instance giver mening, fordi throw skal ændrer typen til Unhandled men så typetjeker vi ikke mere med programerne. vi vil gerne have at chatce skal fixe Unhandled til OK men man kan ikke nædvendigvis lave en handeler som fixer alle cases og derfor vil man nok godt have den siger throw.
-- men denne inplimentasion kan man ikke udfølge begge love på en gang catch throw1 :: catch (throw e) h ≡ h e
-- catch throw2 :: catch t throw ≡ t 
