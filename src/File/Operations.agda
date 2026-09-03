module File.Operations where

open import File.States
open import Data.Unit using (⊤)
open import Data.Char using (Char)
open import Data.Maybe


data FileOp : State → State → Set → Set where
  fOpen : FileOp Closed Open ⊤
  fClose : FileOp Open Closed ⊤
  fGetC : FileOp Open Open (Maybe Char)
  -- fWrite : Char → FileOp Open Open ⊤


