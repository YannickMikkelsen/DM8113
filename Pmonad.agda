module Pmonad where
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
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂)
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
    catch  : ∀ {i j : I} {l} {A : Set l} → M i j A → (resetFlag : InjC I I) → M (resetFlag i) (resetFlag j) A → M i (resetFlag j) A
--    catch : ∀ {i j : I} {l} {A : Set l} → M i j A → (resetFlag : InjC I I) → (∀ {k : I} → M k (resetFlag j) A) → M i (resetFlag j) A

M : ∀ {l} → State → State → Set l → Set (suc zero ⊔ l)
M i j A = (s : State) → s ≡ i → Maybe (Σ[ s' ∈ State ] (s' ≡ j) × A)


pmonadState : PMonad {State} {M}
pmonadState .PMonad.pure x s eq = just (s , eq , x)
(pmonadState PMonad.>>= ma) f s eq with ma s eq
... | just (x , eq' , a) = f a x eq'
... | nothing = nothing



combinedState : Combined {State} {M}
combinedState .Combined.pmonad = pmonadState
combinedState .Combined.look getMem s eq = just (s , eq , getMem s)
combinedState .Combined.set setMem val s eq = just (setMem s val , cong (λ st → setMem st val) eq , tt)
combinedState .Combined.fopen getOC _ setStatus fh s eq = just ((setStatus s SOpen) , cong (λ st → setStatus st SOpen) eq , fh)
combinedState .Combined.fread getOC _ fh s eq with uncons fh
... | just (c , _) = just (s , eq , just c)
... | nothing = just (s , eq , nothing)
combinedState .Combined.fwrite getOC _ fh c s eq = just (s , eq , (fh ++ fromChar c))
combinedState .Combined.fclose getOC _ setStatus s eq = just (setStatus s SClosed , cong (λ st → setStatus st SClosed) eq , tt)
combinedState .Combined.throw setFlag s eq = nothing
combinedState .Combined.catch ma resetFlag mb s refl with ma s refl
... | just (s' , eq' , a) = just ((resetFlag s') , (cong resetFlag eq') , a)
... | nothing = mb (resetFlag s) refl


_>>>=_ = pmonadState .PMonad._>>=_


open Combined combinedState

setFlagOK : InjC State State
setFlagOK (mem , oc , _) = (mem , oc , OK)

setFlagUN : InjC State State
setFlagUN (mem , oc , _) = (mem , oc , Unhandled)


setFlag : InjL State Flag State
setFlag (mem , oc , _) f = (mem , oc , f)


getMem : ProjL State Set
getMem (n , _ , _) = n

getStatus : ProjF State
getStatus (_ , oc , _) = oc

setMem : InjL State ℕ State
setMem (_ , oc , fl) val = ℕ , oc , fl

setOpen : InjF State Open State
setOpen (a , _ , flag) _ = (a , Open , flag)

setClosed : InjF State Closed State
setClosed (a , _ , flag) _ = (a , Closed , flag)

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

ReadOpenSetClose : ∀ {n : Set} → M (n , Closed , OK) (ℕ , Closed , OK) ⊤
ReadOpenSetClose =
  readMem >>>= (λ val →
  (openFile "Hello World") >>>= (λ fh →
  (writeMem 67) >>>= λ _ →
  closeFile ))



failingProg : ∀ {n : Set} → M (n , Closed , OK) (n , Closed , Unhandled) ⊤
failingProg s eq = throw setFlag s eq

setFlagHandler : InjL State Flag State
setFlagHandler (mem , oc , _) f = (mem , Closed , f)

-- handler :  ∀ {n : Set} {oc : OC} {fl : Flag} → (M (n , oc , fl) (n , Closed , Unhandled) ⊤) ⊎ (M (n , oc , fl) (n , Closed , OK) ⊤)
-- handler {n} {Open} {OK} = inj₂ (λ s x → closeFile s x)
-- handler {n} {Open} {Unhandled} = inj₁ (throw setFlagHandler)
-- handler {n} {Closed} {OK} = inj₂ (λ s x → just (s , (x , tt)))
-- handler {n} {Closed} {Unhandled} = inj₂ (set setFlag OK)


handler : ∀ {n : Set} {oc : OC} {fl : Flag} → M (n , oc , fl) (n , Closed , OK) ⊤
handler {n} {Open} {OK} s refl = closeFile s refl
handler {n} {Open} {Unhandled} s refl = ((set setFlag OK) >>>= (λ _ → closeFile)) s refl
handler {n} {Closed} {fl} s eq = set setFlag OK s eq


-- VI skal have et program, hvor når handleren thrower, så en fejl i handleren, så kan handleren fikse det.i

-- Kalder catch på et program, t, t har 2 muligheder, returnere eller fejler, hvis du fejler så kalder man handleren og den handler fikser fejlen, men det er muligt at du kalder throw i din handler, så regl (catch_throw₁ ∷ catch (throw e) h ≡ h e) og catch_throw₂ ∷ catch t throw ≡ t, din handler gør ikke noget, så den cascader det bare længere op. catch_return ∷ catch (return x) h ≡ return x

catchProgram : ∀ {n : Set} → M (n , Closed , OK) (n , Closed , OK) ⊤
catchProgram = catch failingProg setFlagOK handler

-- catch_return ∷ catch (return x) h ≡ return x
catch-return : ∀ {n : Set} {oc : OC} {A : Set}
  (x : A)
  → (h : M (n , oc , OK) (n , oc , OK) A)
  → catch (pmonadState .PMonad.pure x) setFlagOK h (n , oc , OK) refl
  ≡ pmonadState .PMonad.pure x (n , oc , OK) refl
catch-return x h = refl


-- catch_throw₁ ∷ catch (throw e) h ≡ h e
catch-throw1 : ∀ {n : Set} {oc : OC} {fl : Flag} {A : Set}
  (h : M (n , oc , OK) (n , oc , OK) A)
  → catch (throw setFlag) setFlagOK h (n , oc , fl) refl ≡ h (n , oc , OK) refl
catch-throw1 h = refl


-- catch_throw₂ ∷ catch t throw ≡ t
catch-throw2 : ∀ {n m : Set} {oc oc' : OC} {A : Set}
  (t : M (n , oc , OK)(m , oc' , OK) A)
  → catch t setFlagOK (λ s eq → nothing) (n , oc , OK) refl
  ≡ t (n , oc , OK) refl
catch-throw2 t with t (_ , _ , OK) refl
... | just ((_ , _ , OK) , refl , a) = refl
... | nothing = refl

rethrowingHandler : ∀ {n : Set} {oc : OC} {fl : Flag} → M (n , oc , fl) (n , oc , Unhandled) ⊤
rethrowingHandler s eq = throw setFlag s eq

nestedCatchProgram : ∀ {n : Set} → M (n , Closed , OK) (n , Closed , OK) ⊤
nestedCatchProgram = catch (catch failingProg setFlagUN rethrowingHandler) setFlagOK handler

