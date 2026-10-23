module Pmonad.CombinedFile where

open import Data.Unit          using (⊤; tt)
open import Data.Maybe         using (just)
open import Data.Nat           using (ℕ)
open import Data.String        using (String)
open import Data.Product       using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Pmonad.Hexc        using (Free; pure; op; ⊤₁; tt₁; Opr; opr)
open import Pmonad.FHAlg       using (FileOp; ArFile; fopenOp; freadOp; fwriteOp; fcloseOp)
open import Pmonad.Combined

------------------------------------------------------------------------
-- Combined instansieret med filoperationerne som "tredje effekt".
-- runC håndterer kun state og undtagelser; filoperationerne forbliver
-- frie i resultatet. Resultatet af runC er derfor SPORET af filkald.

module FileSys (S : Set) (A : Set₁) where
  open Combined S FileOp ArFile A public

  fopenF : ∀ {V : Set₁} → String → (⊤ → Free Full V) → Free Full V
  fopenF path k = fxF (fopenOp path) k

  freadF : ∀ {V : Set₁} → (String → Free Full V) → Free Full V
  freadF k = fxF freadOp k

  fwriteF : ∀ {V : Set₁} → String → (⊤ → Free Full V) → Free Full V
  fwriteF s k = fxF (fwriteOp s) k

  fcloseF : ∀ {V : Set₁} → (⊤ → Free Full V) → Free Full V
  fcloseF k = fxF fcloseOp k


------------------------------------------------------------------------
-- Programmer og spor
 
module TestFileProg where
  open FileSys ℕ ⊤₁
 
  -- Det lækkende program:
  --
  --   fopen ;
  --   catch (write "x" ; throw ; fclose, pure) ;
  --   fopen ; 
  --   write "hello" ; 
  --   fclose ;
  --
  -- (fclose efter throw kan ikke skrives ud, da throwF ikke har en
  -- fortsættelse; den er netop den, som throw springer over.)
  -- Programmet type-checker i en almindelig monad.
  --
  -- I catchF er h hele resten af programmet, hvis kroppen kaster, og k er
  -- resten, hvis kroppen slutter normalt. Programmet efter catch står
  -- derfor i begge grene (rest).
  rest : Free Full ⊤₁
  rest = fopenF "f" λ _ → fwriteF "hello" λ _ → fcloseF λ _ → pure tt₁
 
  leak : Free Full ⊤₁
  leak =
    fopenF "f" λ _ →
    catchF {W = ⊤}
      (λ j → fwriteF "x" λ _ → throwF)
      rest
      (λ _ → rest)
 
  -- Sporet har to fopen og kun én fclose: den første fil bliver aldrig lukket.
  leak-trace :
    runC leak 0
    ≡ op (opr (fopenOp "f")     λ _ →
      op (opr (fwriteOp "x")    λ _ →
      op (opr (fopenOp "f")     λ _ →
      op (opr (fwriteOp "hello") λ _ →
      op (opr fcloseOp          λ _ →
      pure (just tt₁ , 0))))))
  leak-trace = refl
 
  -- Det korrekte program: handleren lukker filen, så sporet er balanceret.
  good : Free Full ⊤₁
  good =
    fopenF "f" λ _ →
    catchF {W = ⊤}
      (λ j → fwriteF "x" λ _ → throwF)
      (fcloseF λ _ → rest)
      (λ _ → rest)
 
  good-trace :
    runC good 0
    ≡ op (opr (fopenOp "f")     λ _ →
      op (opr (fwriteOp "x")    λ _ →
      op (opr fcloseOp          λ _ →
      op (opr (fopenOp "f")     λ _ →
      op (opr (fwriteOp "hello") λ _ →
      op (opr fcloseOp          λ _ →
      pure (just tt₁ , 0)))))))
  good-trace = refl
 