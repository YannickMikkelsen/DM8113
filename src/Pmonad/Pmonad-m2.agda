module Pmonad.Pmonad-m2 where
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
combinedState .Combined.catch ma resetFlag mb s eq with ma s eq
... | just (s' , eq' , x) = just (s' , eq' , x)
... | nothing = mb (resetFlag s OK) (cong (λ st → resetFlag st OK) eq)