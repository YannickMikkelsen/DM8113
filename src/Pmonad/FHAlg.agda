module Pmonad.FHAlg where

open import Data.Unit  using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; if_then_else_)
open import Data.String        using (String)
open import Data.Char          using (Char)
open import Level using (Level; _⊔_; suc; zero; Lift; lift; lower)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; trans)
open import Data.Product using (_×_; _,_)


record FH : Set where
  constructor fh
  field
    filePath : String

-- Primitive fil-operationer
data FileOp : Set where
  fopenOp  : String → FileOp
  freadOp  : FileOp
  fwriteOp : Char → FileOp
  fcloseOp : FileOp

-- Aritet (returtype for hver operation)
ArFile : FileOp → Set
ArFile (fopenOp _)  = FH            -- Returnerer et file handle
ArFile freadOp      = Maybe Char    -- Returnerer et eventuelt tegn
ArFile (fwriteOp _) = FH            -- Returnerer opdateret file handle
ArFile fcloseOp     = ⊤             -- Returnerer unit