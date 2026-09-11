module Pmonad.Pmonad where
open import Data.Unit    using (⊤; tt)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.Char using (Char)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Function using (_∘_)
open import Data.String  using (String; uncons)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; Σ-syntax; _,_)


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

ProjF : Set → OC → Set
ProjF I S = I → SOC S

ProjFF : Set → Set
ProjFF I = I → OC

InjL : Set → Set → Set → Set
InjL I A J = I → A → J

InjF : Set → OC → Set → Set
InjF I S J = I → SOC S → J



record Combined {I : Set} {M : I → I → Set → Set} : Set₁ where
  field
    pmonad : PMonad {I} {M}
  field
    look : ∀ {i : I} {a : Set} → ProjL I a → M i i a
    set  : ∀ {i j : I} {a : Set} → InjL I a I → a → M i j ⊤
    fopen : ∀ {i j : I} → ProjF I Closed → InjF I Open I → String →  M i j FH
    fread : ∀ {i : I} → (getOC : ProjFF I) → getOC i ≡ Open → FH → M i i (Maybe Char)
    fclose : ∀ {i j : I} →  ProjF I Open → InjF I Closed I → M i j ⊤
    throw : ∀ {i j : I} {A : Set} →  M i j ⊥


-- M : State → State → Set → Set
-- M i j a = State → Maybe ( a × State)



-- open PMonad
-- pmonadState : PMonad {State} {M}
-- pmonadState .pure {i} {A} x j = just (x , j)
-- pmonadState . _>>=_ ma f s with ma s
-- ... | just (a , s₁) = f a s₁
-- ... | nothing = nothing

-- open Combined
-- combinedState : Combined {State} {M}
-- combinedState .pmonad = pmonadState
-- combinedState .look proj s = just (proj s , s)
-- combinedState .set inj a s = just (tt , inj s a)
-- combinedState .fopen proj inj fh s with proj s
-- ... | SClosed = just (fh , (inj s SOpen))
-- combinedState .fread proj fh s with proj s
-- ... | SOpen with uncons fh
-- ... | just (c , fh′) = just ((just c) , s)
-- ... | nothing = just (nothing , s)
-- combinedState .fclose proj inj s with proj s
-- ... | SOpen = just (tt , inj s SClosed)
-- combinedState .throw s = nothing




-- getMem : ProjL State ℕ
-- getMem (n , _) = n

-- getClosed : ProjF State Closed
-- getClosed (n , Closed) = SClosed
-- getClosed (n , Open) = SClosed

-- getOpen : ProjF State Open
-- getOpen (n , Open) = SOpen
-- getOpen (n , Closed) = SOpen


-- setMem : InjL State ℕ State
-- setMem (n , oc) val = val , oc

-- openFile : InjF State Open State
-- openFile (n , _) soc = n , Open


-- closeFile : InjF State Closed State
-- closeFile (n , _) soc = n , Closed

-- ReadOpenSetClose : ∀ {i j : State} → M i j ⊤
-- ReadOpenSetClose {i} {j} x =
--   pmonadState ._>>=_ {i} {i} {i} (combinedState .look {i} getMem) (λ val →
--   pmonadState ._>>=_ {i} {i} {j} (combinedState .fopen {i} {j} getClosed openFile "Hello World") λ fh →
--   pmonadState ._>>=_ {j} {j} {j} (combinedState .set {j} {j} setMem val) (λ _ →
--   combinedState .fclose {j} {i} getOpen closeFile)) x








