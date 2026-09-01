module File.Operations where

open import File.States
open import Data.Unit using (⊤)
open import Data.Char using (Char)

data FileOp : FileState → FileState → Set → Set where
  Open : FileOp Closed Open ⊤
  Close : FileOp Open Closed ⊤
  Read : FileOp Open Open Char
  Write : Char → FileOp Open Open ⊤
