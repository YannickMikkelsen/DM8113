module Pmonad.State where

open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Pmonad.Hexc

------------------------------------------------------------------------
-- 1. State-signaturen i samme stil som Opr

data StP (S : Set) : Set where
  getP : StP S
  putP : S → StP S

ArSt : ∀ {S} → StP S → Set
ArSt {S} getP     = S      -- get giver en S videre
ArSt     (putP _) = ⊤      -- put giver ingenting videre

------------------------------------------------------------------------
-- 2. State-lovene og state-algebraen

module StateLaws (S : Set) where

  Σst : Set₁ → Set₁
  Σst = Opr (StP S) ArSt

  get' : ∀ {V : Set₁} → (S → Free Σst V) → Free Σst V
  get' k = op (opr getP k)

  put' : ∀ {V : Set₁} → S → Free Σst V → Free Σst V
  put' s m = op (opr (putP s) (λ _ → m))

  data SVar : Set₁ where
    tv  : SVar
    kv  : S → SVar
    kv2 : S → S → SVar

  -- get >> t ≡ t
  eqGQ : Equation Σst ⊤ SVar
  eqGQ = (λ _ → get' (λ _ → pure tv)) ≐ (λ _ → pure tv)

  -- put s >> get ≡ put s >> return s
  eqPG : Equation Σst S SVar
  eqPG = (λ s → put' s (get' (λ s' → pure (kv s')))) ≐ (λ s → put' s (pure (kv s)))

  -- get >>= put ≡ return ()
  eqGP : Equation Σst ⊤ SVar
  eqGP = (λ _ → get' (λ s → put' s (pure tv))) ≐ (λ _ → pure tv)

  -- get >>= λ s. get >>= f s ≡ get >>= λ s. f s s
  eqGG : Equation Σst ⊤ SVar
  eqGG = (λ _ → get' (λ s → get' (λ s' → pure (kv2 s s')))) ≐ (λ _ → get' (λ s → pure (kv2 s s)))

  -- put s1 >> put s2 ≡ put s2
  eqPP : Equation Σst (S × S) SVar
  eqPP = (λ{ (s1 , s2) → put' s1 (put' s2 (pure tv)) }) ≐ (λ{ (_ , s2) → put' s2 (pure tv) })

  -- Bærertype: tilstandstransformeren
  St : Set₁ → Set₁
  St R = S → R × S

  algSt : ∀ {R} → Σst (St R) → St R
  algSt (opr getP k)      = λ s → k s s
  algSt (opr (putP s') k) = λ _ → k tt s'

  -- Handler: kør en state-computation fra en starttilstand
  hst : ∀ {X : Set₁} → Free Σst X → St X
  hst m = fold (λ x s → x , s) algSt m

  eqGQ-ok : ∀ {R} → respects {C = St R} algSt eqGQ
  eqGQ-ok ρ tt = refl

  eqPG-ok : ∀ {R} → respects {C = St R} algSt eqPG
  eqPG-ok ρ s = refl

  eqGP-ok : ∀ {R} → respects {C = St R} algSt eqGP
  eqGP-ok ρ tt = refl

  eqGG-ok : ∀ {R} → respects {C = St R} algSt eqGG
  eqGG-ok ρ tt = refl

  eqPP-ok : ∀ {R} → respects {C = St R} algSt eqPP
  eqPP-ok ρ (s1 , s2) = refl

------------------------------------------------------------------------
-- 3. Interaktion Exc ↔ State: eq7/eq8 er allerede generelle i p

module Interaction (S : Set) (A : Set₁) (X : Set) (Y V : Set₁) where
  module E = Eqs (StP S) ArSt A

  -- catch kan skubbes forbi get/put, og throw >>= (get/put) ≡ throw
  eq7-get = E.Inter.eq7-ok getP X Y V
  eq8-get = E.Inter.eq8-ok getP X Y V
  eq7-put = λ (s : S) → E.Inter.eq7-ok (putP s) X Y V
  eq8-put = λ (s : S) → E.Inter.eq8-ok (putP s) X Y V

------------------------------------------------------------------------
-- 4. Tests: Exc + State med hexc' og hst

module Test where
  open StateLaws ℕ

  J₀ = JΣ Σst ⊤₁
  S₀ = Exc J₀ + Σst
  T  = Free S₀ ⊤₁

  run : T → Free Σst (Maybe ⊤₁)
  run = hexc' {Σ = Σst} {A = ⊤₁}

  exec : T → ℕ → Maybe ⊤₁ × ℕ
  exec m = hst (run m)

  throw'' : T
  throw'' = op (i₁ throw)

  put'' : ℕ → T → T
  put'' n m = op (i₂ (opr (putP n) (λ _ → m)))

  get'' : (ℕ → T) → T
  get'' k = op (i₂ (opr getP k))

  catch'' : (J₀ ⊤ → T) → T → (⊤ → T) → T
  catch'' p h k = op (i₁ (catch {A = ⊤} p h k))

  -- put 1; catch (put 2; throw) (return ()) : put 2 overlever (global state)
  t-global : exec (put'' 1 (catch'' (λ j → put'' 2 throw'') (pure tt₁) (λ _ → pure tt₁))) 0
           ≡ (just tt₁ , 2)
  t-global = refl

  -- handleren h ser tilstanden 2 og tæller den op
  t-h-ser-2 : exec (put'' 1 (catch'' (λ j → put'' 2 throw'')
                                    (get'' (λ s → put'' (suc s) (pure tt₁)))
                                    (λ _ → pure tt₁))) 0
            ≡ (just tt₁ , 3)
  t-h-ser-2 = refl

  -- uden fejl kører h ikke, og k fortsætter
  t-ingen-fejl : exec (put'' 1 (catch'' (λ j → put'' 2 (op (i₁ (end j tt))))
                                       (put'' 9 (pure tt₁))
                                       (λ _ → pure tt₁))) 0
               ≡ (just tt₁ , 2)
  t-ingen-fejl = refl

  -- throw uden handler: resultat nothing, men put før throw bevares
  t-uhandlet : exec (put'' 4 throw'') 0 ≡ (nothing , 4)
  t-uhandlet = refl