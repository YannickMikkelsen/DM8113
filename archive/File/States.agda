module File.States where

data State : Set where
  Open   : State
  Closed : State


data SState : State → Set where
  sOpen   : SState Open
  sClosed : SState Closed

  



