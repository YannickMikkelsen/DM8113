module Slop.CombinedFile where

open import Data.Unit          using (⊤; tt)
open import Data.Maybe         using (Maybe; just; nothing)
open import Data.String        using (String)
open import Data.Product       using (_×_; _,_)
open import Data.Nat           using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Slop.Hexc
open import Slop.Lawful
open import Slop.StateSig
open import Slop.FHAlg
open import Slop.ExcGen
open Functor ⦃...⦄

module FileAlg (S : Set) (A : Set₁) where

  -- Signatur: state + fil, begge rene funktorer, ingen Opr
  Sg : Set₁ → Set₁
  Sg = StateOp S + FileOpS

  R : Set₁
  R = Maybe A × S

  D : Set₁
  D = S → HFile R

  αD : Sg D → D
  αD (i₁ (get k))    = λ s → k s s
  αD (i₁ (put s' k)) = λ _ → k s'
  αD (i₂ f)          = λ s → algFile (fmap (λ (k : D) → k s) f)

  lawfulSg : Lawful Sg
  lawfulSg = lawful+ lawfulState lawfulFile

  module G = Gen Sg lawfulSg D αD

  Full : Set₁ → Set₁
  Full = G.S              -- = Exc J + (StateOp S + FileOpS)

  C : Set₁
  C = G.C

  algD : Full C → C
  algD = G.algE

  ----------------------------------------------------------------------
  -- Variabeltyper

  data SVar : Set₁ where
    tv  : SVar
    kv  : S → SVar
    kv2 : S → S → SVar

  data FV : Set₁ where
    tv : FV
    kr : String → FV

  ----------------------------------------------------------------------
  -- State-love

  eqGQ : Equation Full ⊤ SVar
  eqGQ = (λ _ → op (i₂ (i₁ (get (λ _ → pure tv))))) ≐ (λ _ → pure tv)

  eqPG : Equation Full S SVar
  eqPG = (λ s → op (i₂ (i₁ (put s (op (i₂ (i₁ (get (λ s' → pure (kv s'))))))))))
         ≐ (λ s → op (i₂ (i₁ (put s (pure (kv s))))))

  eqGP : Equation Full ⊤ SVar
  eqGP = (λ _ → op (i₂ (i₁ (get (λ s → op (i₂ (i₁ (put s (pure tv))))))))) ≐ (λ _ → pure tv)

  eqGG : Equation Full ⊤ SVar
  eqGG = (λ _ → op (i₂ (i₁ (get (λ s → op (i₂ (i₁ (get (λ s' → pure (kv2 s s')))))))))) 
         ≐ (λ _ → op (i₂ (i₁ (get (λ s → pure (kv2 s s))))))

  eqPP : Equation Full (S × S) SVar
  eqPP = (λ{ (s1 , s2) → op (i₂ (i₁ (put s1 (op (i₂ (i₁ (put s2 (pure tv)))))))) })
         ≐ (λ{ (_ , s2) → op (i₂ (i₁ (put s2 (pure tv)))) })

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

  ----------------------------------------------------------------------
  -- Fil-love

  -- fopen p ; fclose ≡ pure    (for ALLE stier)
  eq-open-close : Equation Full String FV
  eq-open-close = (λ f → op (i₂ (i₂ (fopen f (op (i₂ (i₂ (fclose (pure tv)))))))))
                  ≐ (λ f → pure tv)

  eq-open-close-ok : respects {C = C} algD eq-open-close
  eq-open-close-ok ρ p = refl

  -- write s1 ; write s2 ≡ write s2
  eq-write-write : Equation Full (String × String) FV
  eq-write-write = (λ{ (s1 , s2) → op (i₂ (i₂ (fwrite s1 (op (i₂ (i₂ (fwrite s2 (pure tv)))))))) })
                   ≐ (λ{ (_ , s2) → op (i₂ (i₂ (fwrite s2 (pure tv)))) })

  eq-write-write-ok : respects {C = C} algD eq-write-write
  eq-write-write-ok ρ (s1 , s2) = refl

  -- write s ; read ≡ write s ; pure s
  eq-write-read : Equation Full String FV
  eq-write-read = (λ s → op (i₂ (i₂ (fwrite s (op (i₂ (i₂ (fread (λ r → pure (kr r)))))))))) 
                  ≐ (λ s → op (i₂ (i₂ (fwrite s (pure (kr s))))))

  eq-write-read-ok : respects {C = C} algD eq-write-read
  eq-write-read-ok ρ s = refl


  ----------------------------------------------------------------------
  -- Operationsformer (pladsholdere i eq7-9 og tensor-lovene)

  oGet : ∀ {K : Set₁} → (S → K) → Sg K
  oGet c = i₁ (get c)

  oPut : S → ∀ {K : Set₁} → (⊤ → K) → Sg K
  oPut s c = i₁ (put s (c tt))

  oFopen : String → ∀ {K : Set₁} → (⊤ → K) → Sg K
  oFopen p c = i₂ (fopen p (c tt))

  oFread : ∀ {K : Set₁} → (String → K) → Sg K
  oFread c = i₂ (fread c)

  oFwrite : String → ∀ {K : Set₁} → (⊤ → K) → Sg K
  oFwrite s c = i₂ (fwrite s (c tt))

  oFclose : ∀ {K : Set₁} → (⊤ → K) → Sg K
  oFclose c = i₂ (fclose (c tt))

  nGet : G.Natural S oGet
  nGet f c = refl
  nPut : ∀ s → G.Natural ⊤ (oPut s)
  nPut s f c = refl
  nFopen : ∀ p → G.Natural ⊤ (oFopen p)
  nFopen p f c = refl
  nFread : G.Natural String oFread
  nFread f c = refl
  nFwrite : ∀ s → G.Natural ⊤ (oFwrite s)
  nFwrite s f c = refl
  nFclose : G.Natural ⊤ oFclose
  nFclose f c = refl

  ----------------------------------------------------------------------
  -- Exception-lovene eq1-eq9 mod den samlede algebra

  module ExcLaws (X : Set) (Y V : Set₁) where

    eq1-ok : respects {C = C} algD (G.eq1 X)
    eq1-ok = G.eq1-ok X

    eq2-ok : respects {C = C} algD (G.eq2 X)
    eq2-ok = G.eq2-ok X

    -- eq3 (kræver WF), eq4, eq5, eq6
    open G.Bind X Y V public

    -- eq7-eq9 for hver operation
    module IGet                 = G.Inter S      oGet         nGet         X Y V
    module IPut    (s : S)      = G.Inter ⊤      (oPut s)     (nPut s)     X Y V
    module IFopen  (p : String) = G.Inter ⊤      (oFopen p)   (nFopen p)   X Y V
    module IFread               = G.Inter String oFread       nFread       X Y V
    module IFwrite (s : String) = G.Inter ⊤      (oFwrite s)  (nFwrite s)  X Y V
    module IFclose              = G.Inter ⊤      oFclose      nFclose      X Y V

  ----------------------------------------------------------------------
  -- Tensorlove: state-operationer kommuterer med fil-operationer.
  -- Hypotesen commD er refl i alle 8 tilfælde.

  module TensorLaws where
    module GetFopen  (p : String) = G.Comm S ⊤ oGet nGet (oFopen p)  (nFopen p)  (λ u → refl)
    module GetFread               = G.Comm S String oGet nGet oFread  nFread      (λ u → refl)
    module GetFwrite (s : String) = G.Comm S ⊤ oGet nGet (oFwrite s) (nFwrite s) (λ u → refl)
    module GetFclose              = G.Comm S ⊤ oGet nGet oFclose      nFclose     (λ u → refl)

    module PutFopen  (s : S) (p : String) = G.Comm ⊤ ⊤ (oPut s) (nPut s) (oFopen p)  (nFopen p)  (λ u → refl)
    module PutFread  (s : S)              = G.Comm ⊤ String (oPut s) (nPut s) oFread  nFread      (λ u → refl)
    module PutFwrite (s : S) (t : String) = G.Comm ⊤ ⊤ (oPut s) (nPut s) (oFwrite t) (nFwrite t) (λ u → refl)
    module PutFclose (s : S)              = G.Comm ⊤ ⊤ (oPut s) (nPut s) oFclose      nFclose     (λ u → refl)

------------------------------------------------------------------------
-- Tests: rå træer, ingen opr / smart constructors

module FileExample where
  open FileAlg ℕ ⊤₁          -- S = ℕ, A = ⊤₁

  genF : ⊤₁ → C
  genF x = λ hd s m → (just x , s) , m

  runF : Free Full ⊤₁ → D
  runF t = fold genF algD t (λ s m → (nothing , s) , m)

  -- throw i kroppen: handleren kører, filen lukkes aldrig
  program1 : Free Full ⊤₁
  program1 =
    op (i₂ (i₂ (fopen "f"
      (op (i₁ (catch {A = ⊤}
        (λ j → op (i₂ (i₂ (fwrite "GodMornign" (op (i₁ throw))))))
        (pure tt₁)
        (λ _ → op (i₂ (i₂ (fclose (pure tt₁)))))))
      >>= λ _ →
        op (i₂ (i₂ (fopen "ff"
          (op (i₂ (i₂ (fwrite "hello"
            (op (i₂ (i₂ (fclose (pure tt₁))))))))))))))))

  -- end j tt i kroppen: fortsættelsen k kører, filen lukkes
  program2 : Free Full ⊤₁
  program2 =
    op (i₂ (i₂ (fopen "f"
      (op (i₁ (catch {A = ⊤}
        (λ j → op (i₂ (i₂ (fwrite "GodMornign" (op (i₁ (end j tt)))))))
        (pure tt₁)
        (λ _ → op (i₂ (i₂ (fclose (pure tt₁)))))))
      >>= λ _ →
        op (i₂ (i₂ (fopen "ff"
          (op (i₂ (i₂ (fwrite "hello"
            (op (i₂ (i₂ (fclose (pure tt₁))))))))))))))))

  test-leak : runF program1 0 "init" ≡ ((just tt₁ , 0) , "hello")
  test-leak = refl

  test-good : runF program2 0 "init" ≡ ((just tt₁ , 0) , "hello")
  test-good = refl