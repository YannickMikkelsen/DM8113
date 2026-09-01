module File.States where

data FileState : Set where
  Closed : FileState
  Open : FileState
