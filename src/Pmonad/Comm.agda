module Pmonad.Comm where

open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (ℕ; suc; zero)
open import Data.Product using (_×_; _,_)
open import Level using (zero; suc)
open import Axiom.Extensionality.Propositional using (Extensionality)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Pmonad.Hexc
open import Pmonad.State using (StP; getP; putP; ArSt)

postulate funext : ∀ {a b} → Extensionality a b

-- Cache-signaturen: opslag af en nøgle, svaret er Maybe Val
data CP (Key : Set) : Set where
  lookupP : Key → CP Key

module StateCache (S Key Val : Set) (eqS : S → S → Bool) (b : S) (key : Key) where

  ArC : CP Key → Set
  ArC (lookupP _) = Maybe Val

  -- sammenligning på state-operationernes svar (kun getP bruger den rigtigt)
  _==_ : ∀ {p} → ArSt {S} p → ArSt p → Bool
  _==_ {getP}   = eqS
  _==_ {putP _} _ _ = true

  -- eqComm fra din Eqs.Comm, instantieret: p1 = get, p2 = lookup key
  module C = Eqs.Comm (StP S) ArSt ⊤₁ (StP S) ArSt (CP Key) ArC _==_ getP (lookupP key) b

  -- Fælles bærertype: cachen er et skrivebeskyttet miljø, state er en transformer
  Env : Set
  Env = Key → Maybe Val

  Cs : Set₁ → Set₁
  Cs R = Env → S → R × S

  -- Fælles algebra for state + cache
  alg : ∀ {R} → C.S2 (Cs R) → Cs R
  alg (i₁ (opr getP k))      = λ c s → k s c s
  alg (i₁ (opr (putP s') k)) = λ c _ → k tt c s'
  alg (i₂ (opr (lookupP q) k)) = λ c s → k (c q) c s

  -- Punktvis bevis (ingen aksiomer)
  eqComm-pt : ∀ {R} (ρ : C.KVar → Cs R) (c : Env) (s : S) →
              fold ρ alg (lhs C.eqComm tt) c s ≡ fold ρ alg (rhs C.eqComm tt) c s
  eqComm-pt ρ c s with eqS s b
  ... | true  = refl
  ... | false = refl

  -- respects (Definition 2.1) kræver ≡ på funktioner, så her bruges funext
  eqComm-ok : ∀ {R} → respects {C = Cs R} alg C.eqComm
  eqComm-ok ρ tt = funext (λ c → funext (λ s → eqComm-pt ρ c s))