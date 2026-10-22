module Pmonad.Combined where

open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Pmonad.Hexc
open import Pmonad.State using (StP; getP; putP; ArSt)
open import Pmonad.ExcGen
open Functor ⦃...⦄


module Combined (S : Set) (P : Set) (Ar : P → Set) (A : Set₁) where

  -- samlet signatur: state-operationer (inj₁) + den tredje effekt (inj₂)
  PS : Set
  PS = StP S ⊎ P

  ArS : PS → Set
  ArS (inj₁ q) = ArSt q
  ArS (inj₂ p) = Ar p

  -- resten
  Σ₀ : Set₁ → Set₁
  Σ₀ = Opr P Ar

  Hd : Set₁
  Hd = S → Free Σ₀ (Maybe A × S)

  -- state-algebraen
  αC : Opr PS ArS Hd → Hd
  αC (opr (inj₁ getP)      k) = λ s → k s s
  αC (opr (inj₁ (putP s')) k) = λ _ → k tt s'
  αC (opr (inj₂ p)         k) = λ s → op (opr p (λ b → k b s))


  module G = Gen PS ArS Hd αC

  Full : Set₁ → Set₁
  Full = G.S

  Jc : Set → Set₁
  Jc = G.J

  C : Set₁
  C = G.C

  algC : Full C → C
  algC = G.algE

  genC : A → C
  genC x = λ hd s → pure (just x , s)

  runC : Free Full A → Hd
  runC m = fold genC algC m (λ s → pure (nothing , s))

  -- Smart constructors

  throwF : ∀ {V : Set₁} → Free Full V
  throwF = op (i₁ throw)

  endF : ∀ {V : Set₁} {W : Set} → Jc W → W → Free Full V
  endF j x = op (i₁ (end j x))

  catchF : ∀ {V : Set₁} {W : Set}
         → (Jc W → Free Full V) → Free Full V → (W → Free Full V) → Free Full V
  catchF p h k = op (i₁ (catch p h k))

  getF : ∀ {V : Set₁} → (S → Free Full V) → Free Full V
  getF k = op (i₂ (opr (inj₁ getP) k))

  putF : ∀ {V : Set₁} → S → Free Full V → Free Full V
  putF s m = op (i₂ (opr (inj₁ (putP s)) (λ _ → m)))

  fxF : ∀ {V : Set₁} (p : P) → (Ar p → Free Full V) → Free Full V
  fxF p k = op (i₂ (opr (inj₂ p) k))

  -- Exception-lovene

  module ExcLaws (X : Set) (Y V : Set₁) where

    eq1-ok = G.eq1-ok X
    eq2-ok = G.eq2-ok X

    -- eq3 eq4, eq5, eq6
    open G.Bind X Y V public

    module IGet = G.Inter (inj₁ getP) X Y V
    module IPut (s : S) = G.Inter (inj₁ (putP s)) X Y V

  -- State-lovene mod den samlede algebra (reducerer til refl som før)

  module StateEqs where

    data SVar : Set₁ where
      tv  : SVar
      kv  : S → SVar
      kv2 : S → S → SVar

    eqGQ : Equation Full ⊤ SVar
    eqGQ = (λ _ → getF (λ _ → pure tv)) ≐ (λ _ → pure tv)

    eqPG : Equation Full S SVar
    eqPG = (λ s → putF s (getF (λ s' → pure (kv s')))) ≐ (λ s → putF s (pure (kv s)))

    eqGP : Equation Full ⊤ SVar
    eqGP = (λ _ → getF (λ s → putF s (pure tv))) ≐ (λ _ → pure tv)

    eqGG : Equation Full ⊤ SVar
    eqGG = (λ _ → getF (λ s → getF (λ s' → pure (kv2 s s')))) ≐ (λ _ → getF (λ s → pure (kv2 s s)))

    eqPP : Equation Full (S × S) SVar
    eqPP = (λ{ (s1 , s2) → putF s1 (putF s2 (pure tv)) }) ≐ (λ{ (_ , s2) → putF s2 (pure tv) })

    eqGQ-ok : respects {C = C} algC eqGQ
    eqGQ-ok ρ tt = refl

    eqPG-ok : respects {C = C} algC eqPG
    eqPG-ok ρ s = refl

    eqGP-ok : respects {C = C} algC eqGP
    eqGP-ok ρ tt = refl

    eqGG-ok : respects {C = C} algC eqGG
    eqGG-ok ρ tt = refl

    eqPP-ok : respects {C = C} algC eqPP
    eqPP-ok ρ (s1 , s2) = refl

------------------------------------------------------------------------
-- Eksempelprogrammer: state = ℕ, "tredje effekt" = Fire (P = ⊤, Ar = λ _ → ⊤), A = ⊤₁

module Test where
  open Combined ℕ ⊤ (λ _ → ⊤) ⊤₁

  T : Set₁
  T = Free Full ⊤₁

  R : Set₁
  R = Free Σ₀ (Maybe ⊤₁ × ℕ)

  exec : T → ℕ → R
  exec = runC

  throw'' : T
  throw'' = throwF

  put'' : ℕ → T → T
  put'' = putF

  get'' : (ℕ → T) → T
  get'' = getF

  fire'' : T → T
  fire'' m = fxF tt (λ _ → m)

  end'' : Jc ⊤ → T
  end'' j = endF j tt

  catch'' : (Jc ⊤ → T) → T → (⊤ → T) → T
  catch'' p h k = catchF {W = ⊤} p h k

  ok : ℕ → R
  ok s = pure (just tt₁ , s)

  fail : ℕ → R
  fail s = pure (nothing , s)

  fired : R → R
  fired r = op (opr tt (λ _ → r))

  ----------------------------------------------------------
  -- Grundlæggende

  t-pure : exec (pure tt₁) 5 ≡ ok 5
  t-pure = refl

  t-get : exec (get'' (λ s → put'' (suc s) (pure tt₁))) 5 ≡ ok 6
  t-get = refl

  t-uhandlet : exec (put'' 4 throw'') 0 ≡ fail 4
  t-uhandlet = refl

  ----------------------------------------------------------
  -- Exc + state: state er global og overlever throw

  t-global : exec (put'' 1 (catch'' (λ j → put'' 2 throw'')
                                    (pure tt₁)
                                    (λ _ → pure tt₁))) 0
           ≡ ok 2
  t-global = refl

  t-h-ser-2 : exec (put'' 1 (catch'' (λ j → put'' 2 throw'')
                                     (get'' (λ s → put'' (suc s) (pure tt₁)))
                                     (λ _ → pure tt₁))) 0
            ≡ ok 3
  t-h-ser-2 = refl

  t-ingen-fejl : exec (put'' 1 (catch'' (λ j → put'' 2 (end'' j))
                                        (put'' 9 (pure tt₁))
                                        (λ _ → pure tt₁))) 0
               ≡ ok 2
  t-ingen-fejl = refl

  t-k-kaster : exec (put'' 1 (catch'' (λ j → put'' 2 (end'' j))
                                      (put'' 9 (pure tt₁))
                                      (λ _ → put'' 5 throw''))) 0
             ≡ fail 5
  t-k-kaster = refl

  ----------------------------------------------------------
  -- Tredje effekt (fire) går igennem begge lag

  t-fire-state : exec (put'' 1 (fire'' (get'' (λ s → put'' (suc s) (pure tt₁))))) 0
               ≡ fired (ok 2)
  t-fire-state = refl

  t-fire-throw : exec (put'' 3 (fire'' throw'')) 0 ≡ fired (fail 3)
  t-fire-throw = refl

  t-fire-handler : exec (catch'' (λ j → fire'' throw'')
                                 (put'' 7 (pure tt₁))
                                 (λ _ → pure tt₁)) 0
                 ≡ fired (ok 7)
  t-fire-handler = refl

  t-fire-i-h : exec (catch'' (λ j → put'' 2 throw'')
                             (get'' (λ s → fire'' (put'' (suc s) (pure tt₁))))
                             (λ _ → pure tt₁)) 0
             ≡ fired (ok 3)
  t-fire-i-h = refl

  ----------------------------------------------------------
  -- eq3:  catch (λ j → m >>= end j) throw k  ≡  m >>= k   (m veldannet)

  lhs3 : T → (⊤ → T) → T
  lhs3 m k = catch'' (λ j → m >>= λ _ → end'' j) throw'' k

  rhs3 : T → (⊤ → T) → T
  rhs3 m k = m >>= λ _ → k tt

  m-st : T
  m-st = put'' 2 (fire'' (get'' (λ s → put'' (suc s) (pure tt₁))))

  t-eq3-st : exec (lhs3 m-st (λ _ → put'' 8 (pure tt₁))) 0 ≡ fired (ok 8)
  t-eq3-st = refl
  t-eq3-st' : exec (rhs3 m-st (λ _ → put'' 8 (pure tt₁))) 0 ≡ fired (ok 8)
  t-eq3-st' = refl

  t-eq3-st-throw : exec (lhs3 m-st (λ _ → put'' 9 throw'')) 0 ≡ fired (fail 9)
  t-eq3-st-throw = refl
  t-eq3-st-throw' : exec (rhs3 m-st (λ _ → put'' 9 throw'')) 0 ≡ fired (fail 9)
  t-eq3-st-throw' = refl

  -- m med indre catch hvis krop kaster: den indre handler kører
  m-inner : T
  m-inner = catch'' (λ j → put'' 5 throw'') (fire'' (put'' 6 (pure tt₁))) (λ _ → pure tt₁)

  t-eq3-inner : exec (lhs3 m-inner (λ _ → throw'')) 0 ≡ fired (fail 6)
  t-eq3-inner = refl
  t-eq3-inner' : exec (rhs3 m-inner (λ _ → throw'')) 0 ≡ fired (fail 6)
  t-eq3-inner' = refl

  -- Uden veldannethed er eq3 FALSK: indre krop slutter med pure
  m-pure : T
  m-pure = catch'' (λ j → pure tt₁) (fire'' (pure tt₁)) (λ _ → pure tt₁)

  t-eq3-bad-lhs : exec (lhs3 m-pure (λ _ → throw'')) 0 ≡ fail 0
  t-eq3-bad-lhs = refl
  t-eq3-bad-rhs : exec (rhs3 m-pure (λ _ → throw'')) 0 ≡ fired (fail 0)
  t-eq3-bad-rhs = refl