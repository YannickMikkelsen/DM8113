module IndexedMonad.Definition where

record IxMonad {I : Set} {M : I → I → Set → Set} : Set₁ where
  field
    return : ∀ {i} {A : Set} → A → M i i A
    _>>=_ : ∀ {i j k} {A B : Set} → M i j A → (A → M j k B) → M i k B
