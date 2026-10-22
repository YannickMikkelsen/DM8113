module Pmonad.State where

open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Pmonad.Hexc
open Functor ⦃...⦄

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

  get' : ∀ {Σ : Set₁ → Set₁} {V : Set₁} → (S → Free (Σst + Σ) V) → Free (Σst + Σ) V
  get' k = op (i₁ (opr getP k))

  put' : ∀ {Σ : Set₁ → Set₁} {V : Set₁} → S → Free (Σst + Σ) V → Free (Σst + Σ) V
  put' s m = op (i₁ (opr (putP s) (λ _ → m)))
  
  data SVar : Set₁ where
    tv  : SVar
    kv  : S → SVar
    kv2 : S → S → SVar

  -- get >> t ≡ t
  eqGQ : ∀ {Σ : Set₁ → Set₁} → Equation (Σst + Σ) ⊤ SVar
  eqGQ = (λ _ → get' (λ _ → pure tv)) ≐ (λ _ → pure tv)

  -- put s >> get ≡ put s >> return s
  eqPG : ∀ {Σ : Set₁ → Set₁} → Equation (Σst + Σ) S SVar
  eqPG = (λ s → put' s (get' (λ s' → pure (kv s')))) ≐ (λ s → put' s (pure (kv s)))

  -- get >>= put ≡ return ()
  eqGP : ∀ {Σ : Set₁ → Set₁} → Equation (Σst + Σ) ⊤ SVar
  eqGP = (λ _ → get' (λ s → put' s (pure tv))) ≐ (λ _ → pure tv)

  -- get >>= λ s. get >>= f s ≡ get >>= λ s. f s s
  eqGG : ∀ {Σ : Set₁ → Set₁} → Equation (Σst + Σ) ⊤ SVar
  eqGG = (λ _ → get' (λ s → get' (λ s' → pure (kv2 s s')))) ≐ (λ _ → get' (λ s → pure (kv2 s s)))

  -- put s1 >> put s2 ≡ put s2
  eqPP : ∀ {Σ : Set₁ → Set₁} → Equation (Σst + Σ) (S × S) SVar
  eqPP = (λ{ (s1 , s2) → put' s1 (put' s2 (pure tv)) }) ≐ (λ{ (_ , s2) → put' s2 (pure tv) })
  -- Bærertype: tilstandstransformeren
  -- St : Set₁ → Set₁
  -- St R = S → R × S

  -- algSt : ∀ {R} → Σst (St R) → St R
  -- algSt (opr getP k)      = λ s → k s s
  -- algSt (opr (putP s') k) = λ _ → k tt s'
  St : (Σ : Set₁ → Set₁) → Set₁ → Set₁
  St Σ R = S → Free Σ (R × S)

  algSt : ∀ {Σ R} ⦃ _ : Functor Σ ⦄ → (Σst + Σ) (St Σ R) → St Σ R
  algSt (i₁ (opr getP k))      = λ s → k s s
  algSt (i₁ (opr (putP s') k)) = λ _ → k tt s'
  algSt (i₂ x)                 = λ s → op (fmap (λ m → m s) x)

  genSt : ∀ {Σ R} → R → St Σ R
  genSt x = λ s → pure (x , s)
  -- Handler: kør en state-computation fra en starttilstand
  hst : ∀ {Σ : Set₁ → Set₁} ⦃ _ : Functor Σ ⦄ {X : Set₁}
      → Free (Σst + Σ) X → St Σ X
  hst m = fold genSt algSt m

  eqGQ-ok : ∀ {Σ R} ⦃ _ : Functor Σ ⦄ → respects {C = St Σ R} algSt (eqGQ {Σ})
  eqGQ-ok ρ tt = refl

  eqPG-ok : ∀ {Σ R} ⦃ _ : Functor Σ ⦄ → respects {C = St Σ R} algSt (eqPG {Σ})
  eqPG-ok ρ s = refl

  eqGP-ok : ∀ {Σ R} ⦃ _ : Functor Σ ⦄ → respects {C = St Σ R} algSt (eqGP {Σ})
  eqGP-ok ρ tt = refl

  eqGG-ok : ∀ {Σ R} ⦃ _ : Functor Σ ⦄ → respects {C = St Σ R} algSt (eqGG {Σ})
  eqGG-ok ρ tt = refl

  eqPP-ok : ∀ {Σ R} ⦃ _ : Functor Σ ⦄ → respects {C = St Σ R} algSt (eqPP {Σ})
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

  Σ₀ = Σst + Fire                      -- state + fire som "resten"
  J₀ = JΣ Σ₀ ⊤₁
  S₀ = Exc J₀ + Σ₀
  T  = Free S₀ ⊤₁
  R  = Free Fire (Maybe ⊤₁ × ℕ)

  run : T → Free Σ₀ (Maybe ⊤₁)
  run = hexc' {Σ = Σ₀} {A = ⊤₁}

  exec : T → ℕ → R
  exec m = hst {Σ = Fire} (run m)

  -- smart constructors
  throw'' : T
  throw'' = op (i₁ throw)

  put'' : ℕ → T → T
  put'' n m = op (i₂ (i₁ (opr (putP n) (λ _ → m))))

  get'' : (ℕ → T) → T
  get'' k = op (i₂ (i₁ (opr getP k)))

  fire'' : T → T
  fire'' m = op (i₂ (i₂ (fire m)))

  end'' : J₀ ⊤ → T
  end'' j = op (i₁ (end j tt))

  catch'' : (J₀ ⊤ → T) → T → (⊤ → T) → T
  catch'' p h k = op (i₁ (catch {A = ⊤} p h k))

  -- forventede resultater
  ok : ℕ → R
  ok s = pure (just tt₁ , s)

  fail : ℕ → R
  fail s = pure (nothing , s)

  fired : R → R
  fired r = op (fire r)

  ----------------------------------------------------------
  -- Grundlæggende

  t-pure : exec (pure tt₁) 5 ≡ ok 5
  t-pure = refl

  t-get : exec (get'' (λ s → put'' (suc s) (pure tt₁))) 5 ≡ ok 6
  t-get = refl

  -- throw uden handler: nothing, men tilstanden bevares
  t-uhandlet : exec (put'' 4 throw'') 0 ≡ fail 4
  t-uhandlet = refl

  ----------------------------------------------------------
  -- Exc + state: state er global og overlever throw

  -- put 1; catch (put 2; throw) (return ()) : put 2 overlever
  t-global : exec (put'' 1 (catch'' (λ j → put'' 2 throw'')
                                    (pure tt₁)
                                    (λ _ → pure tt₁))) 0
           ≡ ok 2
  t-global = refl

  -- handleren ser tilstanden 2 og tæller den op
  t-h-ser-2 : exec (put'' 1 (catch'' (λ j → put'' 2 throw'')
                                     (get'' (λ s → put'' (suc s) (pure tt₁)))
                                     (λ _ → pure tt₁))) 0
            ≡ ok 3
  t-h-ser-2 = refl

  -- uden fejl kører h ikke
  t-ingen-fejl : exec (put'' 1 (catch'' (λ j → put'' 2 (end'' j))
                                        (put'' 9 (pure tt₁))
                                        (λ _ → pure tt₁))) 0
               ≡ ok 2
  t-ingen-fejl = refl

  -- k kører efter end, og dens throw fanges ikke af h
  t-k-kaster : exec (put'' 1 (catch'' (λ j → put'' 2 (end'' j))
                                      (put'' 9 (pure tt₁))
                                      (λ _ → put'' 5 throw''))) 0
             ≡ fail 5
  t-k-kaster = refl

  ----------------------------------------------------------
  -- Andre operationer (fire) passerer igennem begge handlere

  -- fire ser den aktuelle tilstand, og fortsættelsen får den med
  t-fire-state : exec (put'' 1 (fire'' (get'' (λ s → put'' (suc s) (pure tt₁))))) 0
               ≡ fired (ok 2)
  t-fire-state = refl

  -- effekt før throw bevares, og tilstanden også
  t-fire-throw : exec (put'' 3 (fire'' throw'')) 0 ≡ fired (fail 3)
  t-fire-throw = refl

  -- fire i catch-kroppen, derefter throw: handleren kører bagefter
  t-fire-handler : exec (catch'' (λ j → fire'' throw'')
                                 (put'' 7 (pure tt₁))
                                 (λ _ → pure tt₁)) 0
                 ≡ fired (ok 7)
  t-fire-handler = refl

  -- fire i handleren ser tilstanden fra kroppen
  t-fire-i-h : exec (catch'' (λ j → put'' 2 throw'')
                             (get'' (λ s → fire'' (put'' (suc s) (pure tt₁))))
                             (λ _ → pure tt₁)) 0
             ≡ fired (ok 3)
  t-fire-i-h = refl

  ----------------------------------------------------------
  -- eq3 med state: catch (λ j → m >>= end j) throw k ≡ m >>= k

  lhs3 : T → (⊤ → T) → T
  lhs3 m k = catch'' (λ j → m >>= λ _ → end'' j) throw'' k

  rhs3 : T → (⊤ → T) → T
  rhs3 m k = m >>= λ _ → k tt

  m-st : T
  m-st = put'' 2 (fire'' (get'' (λ s → put'' (suc s) (pure tt₁))))

  t-eq3-st : exec (lhs3 m-st (λ _ → put'' 8 (pure tt₁))) 0
           ≡ exec (rhs3 m-st (λ _ → put'' 8 (pure tt₁))) 0
  t-eq3-st = refl

  t-eq3-st-throw : exec (lhs3 m-st (λ _ → throw'')) 0
                 ≡ exec (rhs3 m-st (λ _ → throw'')) 0
  t-eq3-st-throw = refl