module IndexedMonad.FH where
open import Data.Unit    using (⊤; tt)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.Char using (Char)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Function using (_∘_)
open import Data.String  using (String)
open import IndexedMonad.Definition



data State : Set where
  Open   : State
  Closed : State

data SState : State → Set where
  sOpen   : SState Open
  sClosed : SState Closed

FilePath : Set
FilePath = String

FH : Pred State → Pred State
FH = ((FilePath := Closed) :>>: SState)  --fopen
  :+: (((⊤ := Open) :>>: (Maybe Char := Open))  --fGetC
  :+: ((⊤ := Open) :>>: (⊤ := Closed)))   --fClose


pattern FOpen p k = Do(InL( V p :& k))
pattern FGetC k = Do(InR(InL( V tt :& k)))
pattern FClose k = Do(InR(InR(V tt :& k)))


fOpen : FilePath → :∗ FH SState Closed
fOpen FilePath = FOpen FilePath Ret

fGetC : :∗ FH (Maybe Char := Open) Open
fGetC = FGetC Ret

fClose : :∗ FH (⊤ := Closed) Open
fClose = FClose Ret

FH-IFunctor : IFunctor FH
FH-IFunctor = instance1 instance0 (instance1 instance0 instance0)


FH-IMonad : IMonad (:∗ FH)
FH-IMonad = instance3 FH-IFunctor

open Bind FH-IMonad


readFirstChar : FilePath → :∗ FH (Maybe Char := Closed) Closed
readFirstChar  fp = (fOpen fp) ?>= λ {sOpen → fGetC 
                               =>= (λ c → fClose 
                               =>= λ _ → Ret ((V c)))
                                ; sClosed → Ret ((V nothing))}


-- readFirstChar : ∀ {m} → FilePath → :∗ PRO (Maybe Char := (Closed , m)) (Closed , m)
-- readFirstChar {m} fp = (fOpen fp) ?>= λ { (sOpen  , refl) → fGetC 
--                                   =>= λ c → fClose 
--                                   =>= λ _ → Ret (V c)
--                                   ; (sClosed , refl) → Ret (V nothing) }