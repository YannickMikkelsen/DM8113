module Pmonad.CombinedFile where

open import Data.Unit          using (⊤; tt)
open import Data.Maybe         using (Maybe; just; nothing)
open import Data.Nat           using (ℕ; suc)
open import Data.String        using (String)
open import Data.Char          using (Char)
open import Data.Product       using (_×_; _,_)
open import Data.Sum           using (inj₂; _⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Pmonad.Hexc        using (Free; pure; op; ⊤₁; tt₁; Opr; opr)
open import Pmonad.FHAlg       using (FileOp; ArFile; fopenOp; freadOp; fwriteOp; fcloseOp; FH)
open import Pmonad.Combined

-- Vi instansierer Combined med State = ℕ (eller din egen tilstandstype)
-- og P = FileOp, Ar = ArFile.
module FileSys (S : Set) (A : Set₁) where
  open Pmonad.Combined.Combined S FileOp ArFile A public

  -- Ekstra smart constructors specifik for File-operationerne i det kombinerede system
  fopenF : ∀ {V : Set₁} → String → (FH → Free Full V) → Free Full V
  fopenF path k = fxF (fopenOp path) k

  freadF : ∀ {V : Set₁} → (Maybe Char → Free Full V) → Free Full V
  freadF k = fxF freadOp k

  fwriteF : ∀ {V : Set₁} → Char → (FH → Free Full V) → Free Full V
  fwriteF c k = fxF (fwriteOp c) k

  fcloseF : ∀ {V : Set₁} → (⊤ → Free Full V) → Free Full V
  fcloseF k = fxF fcloseOp k


-- Test/Eksempel modul hvor vi kører et konkret program
module TestFileProg where
  open FileSys ℕ ⊤₁

  -- Eksempel på et kombineret program med Fil-I/O, State og Scoped Exceptions!
  myProgram : Free Full ⊤₁
  myProgram =
    catchF
      (λ j → fopenF "test.txt" λ h →
             putF 42 (endF j tt))   -- Åbner fil, opdaterer tilstand til 42 og afslutter succesfuldt
      (putF 0 throwF)               -- Handler hvis p kaster fejl
      (λ _ → pure tt₁)

  -- Kørsel af programmet via catamorfismen runC
  test-run : runC myProgram 0 ≡ op (opr (fopenOp "test.txt") (λ h → pure (just tt₁ , 42)))
  test-run = refl
