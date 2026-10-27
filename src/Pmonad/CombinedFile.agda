module Pmonad.CombinedFile where

open import Data.Unit          using (⊤; tt)
open import Data.Maybe         using (Maybe; just; nothing)
open import Data.String        using (String)
open import Data.Sum           using (_⊎_; inj₁; inj₂)
open import Data.Product       using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ)

open import Pmonad.Hexc
open import Pmonad.State  using (StP; getP; putP; ArSt)
open import Pmonad.FHAlg  using (FileOp; ArFile; fopenOp; freadOp; fwriteOp; fcloseOp
                                ; HFile; algFile)
open import Pmonad.ExcGen
open Functor ⦃...⦄

module FileAlg (S : Set) (A : Set₁) where

  -- Én signatur: operationsnavne
  data Ops : Set where
    st : StP S → Ops          -- state-operation (getP, putP s)
    fl : FileOp → Ops         -- fil-operation (fopenOp, freadOp, ...)

  ArOps : Ops → Set
  ArOps (st q) = ArSt q
  ArOps (fl f) = ArFile f

  R : Set₁
  R = Maybe A × S

  D : Set₁
  D = S → HFile R

  αD : Opr Ops ArOps D → D
  αD (opr (st getP)      k) = λ s → k s s
  αD (opr (st (putP s')) k) = λ _ → k tt s'
  αD (opr (fl f)         k) = λ s → algFile (opr f (λ b → k b s))

  module G = Gen Ops ArOps D αD     -- Gen er uændret

  Full : Set₁ → Set₁
  Full = G.S

  C : Set₁
  C = G.C

  algD : Full C → C
  algD = G.algE

  getF : ∀ {V : Set₁} → (S → Free Full V) → Free Full V
  getF k = op (i₂ (opr (st getP) k))

  putF : ∀ {V : Set₁} → S → Free Full V → Free Full V
  putF s m = op (i₂ (opr (st (putP s)) (λ _ → m)))

  fxF : ∀ {V : Set₁} (f : FileOp) → (ArFile f → Free Full V) → Free Full V
  fxF f k = op (i₂ (opr (fl f) k))

    -- smart constructors for fil
  fopenF : ∀ {V : Set₁} → String → (⊤ → Free Full V) → Free Full V
  fopenF p k = fxF (fopenOp p) k

  freadF : ∀ {V : Set₁} → (String → Free Full V) → Free Full V
  freadF k = fxF freadOp k

  fwriteF : ∀ {V : Set₁} → String → (⊤ → Free Full V) → Free Full V
  fwriteF s k = fxF (fwriteOp s) k

  fcloseF : ∀ {V : Set₁} → (⊤ → Free Full V) → Free Full V
  fcloseF k = fxF fcloseOp k

  -- variable: tv = "()" og kr = en læst streng
  data FV : Set₁ where
    tv : FV
    kr : String → FV

    -- fopen p ; fclose ≡ pure     (for ALLE stier p)
  eq-open-close : Equation Full String FV
  eq-open-close =
    (λ f → fopenF f (λ _ → fcloseF (λ _ → pure tv)))
    ≐ (λ f → pure tv)

  eq-open-close-ok : respects {C = C} algD eq-open-close
  eq-open-close-ok ρ p = refl

  -- write s1 ; write s2 ≡ write s2
  eq-write-write : Equation Full (String × String) FV
  eq-write-write =
    (λ{ (s1 , s2) → fwriteF s1 (λ _ → fwriteF s2 (λ _ → pure tv)) })
    ≐ (λ{ (_ , s2) → fwriteF s2 (λ _ → pure tv) })

  eq-write-write-ok : respects {C = C} algD eq-write-write
  eq-write-write-ok ρ (s1 , s2) = refl

  -- write s ; read ≡ write s ; pure s
  eq-write-read : Equation Full String FV
  eq-write-read =
    (λ s → fwriteF s (λ _ → freadF (λ r → pure (kr r))))
    ≐ (λ s → fwriteF s (λ _ → pure (kr s)))

  eq-write-read-ok : respects {C = C} algD eq-write-read
  eq-write-read-ok ρ s = refl

  data SVar : Set₁ where
    tv  : SVar
    kv  : S → SVar
    kv2 : S → S → SVar

  -- get >> t ≡ t
  eqGQ : Equation Full ⊤ SVar
  eqGQ = (λ _ → getF (λ _ → pure tv)) ≐ (λ _ → pure tv)

  -- put s >> get ≡ put s >> return s
  eqPG : Equation Full S SVar
  eqPG = (λ s → putF s (getF (λ s' → pure (kv s')))) ≐ (λ s → putF s (pure (kv s)))

  -- get >>= put ≡ return ()
  eqGP : Equation Full ⊤ SVar
  eqGP = (λ _ → getF (λ s → putF s (pure tv))) ≐ (λ _ → pure tv)

  -- get >>= λ s. get >>= f s ≡ get >>= λ s. f s s
  eqGG : Equation Full ⊤ SVar
  eqGG = (λ _ → getF (λ s → getF (λ s' → pure (kv2 s s')))) ≐ (λ _ → getF (λ s → pure (kv2 s s)))

  -- put s1 >> put s2 ≡ put s2
  eqPP : Equation Full (S × S) SVar
  eqPP = (λ{ (s1 , s2) → putF s1 (putF s2 (pure tv)) }) ≐ (λ{ (_ , s2) → putF s2 (pure tv) })

  eqGQ-ok : respects {C = C} algD eqGQ
  eqGQ-ok ρ tt = refl

  eqPG-ok : respects {C = C} algD eqPG
  eqPG-ok ρ s = refl

  eqGP-ok : respects {C = C} algD eqGP
  eqGP-ok ρ tt = refl

  eqGG-ok : respects {C = C} algD eqGG
  eqGG-ok ρ tt = refl

  eqPP-ok : respects {C = C} algD eqPP
  eqPP-ok ρ (s1 , s2) = refl


  module ExcLaws (X : Set) (Y V : Set₁) where

    -- eq1, eq2: catch med end / throw som krop
    eq1-ok : respects {C = C} algD (G.eq1 X)
    eq1-ok = G.eq1-ok X

    eq2-ok : respects {C = C} algD (G.eq2 X)
    eq2-ok = G.eq2-ok X

    -- eq3-eq6 (eq3 kræver WF), eq4, eq5, eq6
    open G.Bind X Y V public

    -- eq7-eq9 for hver operation
        -- eq7-eq9 for hver operation
    module IGet                 = G.Inter (st getP) X Y V
    module IPut  (s : S)        = G.Inter (st (putP s)) X Y V
    module IFopen  (p : String) = G.Inter (fl (fopenOp p)) X Y V
    module IFread               = G.Inter (fl freadOp) X Y V
    module IFwrite (s : String) = G.Inter (fl (fwriteOp s)) X Y V
    module IFclose              = G.Inter (fl fcloseOp) X Y V





------------------------------------------------------------------------------

module FileExample where
  open FileAlg ℕ ⊤₁          -- S = ℕ, A = ⊤₁

  -- generator og kørsel via algD
  genF : ⊤₁ → C
  genF x = λ hd s m → (just x , s) , m

  runF : Free Full ⊤₁ → D
  runF t = fold genF algD t (λ s m → (nothing , s) , m)

  no-close : Free Full ⊤₁
  no-close =
    op (i₂ (opr (fl (fopenOp "f")) (λ _ →
      (op (i₁ (catch {A = ⊤}
        (λ j → op (i₂ (opr (fl (fwriteOp "x")) (λ _ →
                 op (i₁ throw)))))
        (pure tt₁)
        (λ _ → op (i₂ (opr (fl fcloseOp) (λ _ → pure tt₁))))))
      >>= (λ _ →
        op (i₂ (opr (fl (fopenOp "f")) (λ _ →
          op (i₂ (opr (fl (fwriteOp "hello")) (λ _ →
            op (i₂ (opr (fl fcloseOp) (λ _ →
              pure tt₁))))))))))))))



  close : Free Full ⊤₁
  close =
    op (i₂ (opr (fl (fopenOp "f")) (λ _ →
      (op (i₁ (catch {A = ⊤}
        (λ j → op (i₂ (opr (fl (fwriteOp "x")) (λ _ →
                 op (i₁ (end j tt))))))
        (pure tt₁)
        (λ _ → op (i₂ (opr (fl fcloseOp) (λ _ → pure tt₁))))))
      >>= (λ _ →
        op (i₂ (opr (fl (fopenOp "f")) (λ _ →
          op (i₂ (opr (fl (fwriteOp "hello")) (λ _ →
            op (i₂ (opr (fl fcloseOp) (λ _ →
              pure tt₁))))))))))))))


  test : runF no-close 0 "init" ≡ ((just tt₁ , 0) , "hello")
  test = refl


  test1 : runF close 0 "init" ≡ ((just tt₁ , 0) , "hello")
  test1 = refl