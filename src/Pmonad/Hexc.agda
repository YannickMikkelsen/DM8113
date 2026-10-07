module Pmonad.Hexc where

open import Data.Unit  using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)

record ⊤₁ : Set₁ where
  constructor tt₁

-- Free Σ A = pure A | op (Σ (Free Σ A))
{-# NO_POSITIVITY_CHECK #-}
data Free (Σ : Set₁ → Set₁) (A : Set₁) : Set₁ where
  pure : A → Free Σ A
  op   : Σ (Free Σ A) → Free Σ A

record Functor (F : Set₁ → Set₁) : Set₂ where
  field fmap : ∀ {X Y} → (X → Y) → F X → F Y
open Functor ⦃...⦄

{-# TERMINATING #-}
_>>=_ : ∀ {Σ A B} ⦃ _ : Functor Σ ⦄ → Free Σ A → (A → Free Σ B) → Free Σ B
pure x >>= k = k x
op f   >>= k = op (fmap (_>>= k) f)

-- (F + G) K
data _+_ (F G : Set₁ → Set₁) (K : Set₁) : Set₁ where
  i₁ : F K → (F + G) K
  i₂ : G K → (F + G) K

data Fire (K : Set₁) : Set₁ where
  fire : K → Fire K


data Exc (J : Set → Set₁) (K : Set₁) : Set₁ where
  throw : Exc J K
  end   : {A : Set} → J A → A → Exc J K
  catch : {A : Set} → (J A → K) → K → (A → K) → Exc J K

-- end j x >>= k = end j x
instance
  fExc : ∀ {J} → Functor (Exc J)
  fExc = record { fmap = λ where
    f (throw)       → throw
    f (end j x)     → end j x
    f (catch b h k) → catch (λ j → f (b j)) (f h) (λ x → f (k x)) }


prog : ∀ {J} → Free (Exc J + Fire) ⊤₁
prog = op (i₁ (catch {A = ⊤}
                 (λ j → op (i₁ (end j tt))) 
                 (op (i₂ (fire (pure tt₁))))
                 (λ _ → pure tt₁)))



JΣ : (Σ : Set₁ → Set₁) → (R : Set₁) → Set → Set₁
JΣ Σ R X = X → Free Σ (Maybe R)


-- {-# TERMINATING #-}
-- hexc : ∀ {Σ A} ⦃ _ : Functor Σ ⦄
--      → Free (Exc (JΣ Σ A) + Σ) A → Free Σ (Maybe A)
-- hexc (pure x) = pure (just x)
-- hexc (op (i₁ throw)) = pure nothing
-- hexc (op (i₁ (end j x))) = j x
-- hexc (op (i₁ (catch p h k))) = --er ikke rekdig for lige nu siger vi hvis k fajler kører vi h der er ikke rekdigt. det skal værer hvis p og kun p fejler kører vi h.
--   hexc (p (λ x → hexc (k x))) >>= λ where
--     (just a) → pure (just a)
--     nothing  → hexc h
-- hexc (op (i₂ x)) = op (fmap hexc x)



{-# TERMINATING #-}
go : ∀ {Σ A} ⦃ _ : Functor Σ ⦄
   → Free (Exc (JΣ Σ A) + Σ) A → Free Σ (Maybe A) → Free Σ (Maybe A)
go (pure x)                hd = pure (just x)
go (op (i₁ throw))         hd = hd
go (op (i₁ (end j x)))     hd = j x
go (op (i₁ (catch p h k))) hd = go (p (λ x → go (k x) hd)) (go h hd)
go (op (i₂ x))             hd = op (fmap (λ m → go m hd) x)

hexc : ∀ {Σ A} ⦃ _ : Functor Σ ⦄
     → Free (Exc (JΣ Σ A) + Σ) A → Free Σ (Maybe A)
hexc m = go m (pure nothing)