module Slopp.PHexc where

open import Data.Maybe using (Maybe; just; nothing)
open import Level using (Level; _⊔_; suc; zero)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; trans)

postulate
  funext : ∀ {a b} {A : Set a} {B : A → Set b} {f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g

------------------------------------------------------------------------
-- Free indekseret monade: Free Σ A i j = beregning fra tilstand i til j

{-# NO_POSITIVITY_CHECK #-}
data Free {l : Level} {I : Set}
          (Σ : (I → I → Set l) → (I → I → Set l))
          (A : Set l) : I → I → Set l where
  pure : ∀ {i}   → A → Free Σ A i i
  op   : ∀ {i j} → Σ (Free Σ A) i j → Free Σ A i j

record Functor {l : Level} {I : Set}
               (F : (I → I → Set l) → (I → I → Set l)) : Set (suc l) where
  field
    fmap : ∀ {X Y} {j j'} → (∀ {i} → X i j → Y i j') → ∀ {i} → F X i j → F Y i j'

open Functor ⦃...⦄

{-# TERMINATING #-}
_>>=_ : ∀ {l} {I : Set} {Σ : (I → I → Set l) → (I → I → Set l)} {A B : Set l}
        ⦃ _ : Functor Σ ⦄ {i j}
      → Free Σ A i j → (A → Free Σ B j j) → Free Σ B i j
pure x >>= f = f x
op s   >>= f = op (fmap (λ m → m >>= f) s)

{-# TERMINATING #-}
fold : ∀ {I} {Σ : (I → I → Set₁) → (I → I → Set₁)} {C : I → I → Set₁} ⦃ _ : Functor Σ ⦄
         {A : Set₁} {j : I}
     → (A → C j j)
     → (∀ {a} → Σ C a j → C a j)
     → ∀ {i} → Free Σ A i j → C i j
fold gen alg (pure x) = gen x
fold gen alg (op t)   = alg (fmap (fold gen alg) t)

------------------------------------------------------------------------
-- Signaturer

data _+_ {I : Set} (F G : (I → I → Set₁) → (I → I → Set₁))
         (X : I → I → Set₁) : I → I → Set₁ where
  i₁ : ∀ {i j} → F X i j → (F + G) X i j
  i₂ : ∀ {i j} → G X i j → (F + G) X i j

instance
  Functor+ : ∀ {I} {F G : (I → I → Set₁) → (I → I → Set₁)}
           → ⦃ Functor F ⦄ → ⦃ Functor G ⦄ → Functor (F + G)
  Functor+ = record
    { fmap = λ where
        f (i₁ s) → i₁ (fmap f s)
        f (i₂ s) → i₂ (fmap f s) }

data Fire {I : Set} (K : I → I → Set₁) : I → I → Set₁ where
  fire : ∀ {i j} → K i j → Fire K i j

instance
  fFire : ∀ {I} → Functor (Fire {I})
  fFire = record { fmap = λ where f (fire x) → fire (f x) }

data Abort {I : Set} (K : I → I → Set₁) : I → I → Set₁ where
  abort : ∀ {i j} → Abort K i j

instance
  fAbort : ∀ {I} → Functor (Abort {I})
  fAbort = record { fmap = λ where f abort → abort }

-- Opr: operationen går fra i til m, fortsættelsen fra m til j
data Opr {I : Set} (P : I → I → Set) (Ar : ∀ {i m} → P i m → Set)
         (K : I → I → Set₁) : I → I → Set₁ where
  opr : ∀ {i m j} (p : P i m) → (Ar p → K m j) → Opr P Ar K i j

instance
  fOpr : ∀ {I} {P : I → I → Set} {Ar : ∀ {i m} → P i m → Set}
       → Functor (Opr P Ar)
  fOpr = record { fmap = λ where f (opr p c) → opr p (λ b → f (c b)) }

-- Exc: J k A = et hop fra tilstand k med en A
data Exc {I : Set}
         (J : I → Set → Set₁)
         (K : I → I → Set₁)
         : I → I → Set₁ where

  throw : ∀ {i j} → Exc J K i j

  end   : ∀ {k j} {A : Set} → J k A → A → Exc J K k j

  catch : ∀ {i j k} {A : Set}
        → (J k A → K i j)
        → ((s : I) → K s j)
        → (A → K k j)
        → Exc J K i j

fmapExc : ∀ {I} {J : I → Set → Set₁} {X Y : I → I → Set₁} {j j'}
        → (∀ {i} → X i j → Y i j')
        → ∀ {i} → Exc J X i j → Exc J Y i j'
fmapExc f throw         = throw
fmapExc f (end l x)     = end l x
fmapExc f (catch p h k) = catch (λ l → f (p l)) (λ s → f (h s)) (λ x → f (k x))

instance
  fExc : ∀ {I} {J : I → Set → Set₁} → Functor (Exc J)
  fExc = record { fmap = fmapExc }

------------------------------------------------------------------------
-- Algebra for Exc

-- hop til en fortsættelse, der starter i k, tager en A og slutter i j₀
JΣ : ∀ {I} → ((I → I → Set₁) → (I → I → Set₁)) → Set₁ → I → I → Set → Set₁
JΣ Σ R j₀ k A = A → Free Σ (Maybe R) k j₀

T : ∀ {I} → (Σ : (I → I → Set₁) → (I → I → Set₁)) → Set₁ → I → I → Set₁
T Σ A i j = Free Σ (Maybe A) i j

-- givet en handler, der kan køres fra enhver fejltilstand s og slutter i j,
-- får vi en beregning fra i til j
H : ∀ {I} → (Σ : (I → I → Set₁) → (I → I → Set₁)) → Set₁ → I → I → Set₁
H {I} Σ A i j = ((s : I) → T Σ A s j) → T Σ A i j

genH : ∀ {I} {Σ : (I → I → Set₁) → (I → I → Set₁)} {A : Set₁} {i : I}
     → A → H Σ A i i
genH x = λ hd → pure (just x)

algH : ∀ {I} {Σ : (I → I → Set₁) → (I → I → Set₁)} {A : Set₁} ⦃ _ : Functor Σ ⦄ {j₀ : I}
     → ∀ {i} → (Exc (JΣ Σ A j₀) + Σ) (H Σ A) i j₀ → H Σ A i j₀
algH {i = i} (i₁ throw) = λ hd → hd i
algH (i₁ (end l x))     = λ hd → l x
algH (i₁ (catch p h k)) = λ hd → p (λ x → k x hd) (λ s → h s hd)
algH (i₂ x)             = λ hd → op (fmap (λ m → m hd) x)

-- den yderste throw bliver til abort
hexc : ∀ {I} {Σ' : (I → I → Set₁) → (I → I → Set₁)} {A : Set₁} ⦃ _ : Functor Σ' ⦄
     → ∀ {i j} → Free (Exc (JΣ (Abort + Σ') A j) + (Abort + Σ')) A i j
     → T (Abort + Σ') A i j
hexc {Σ' = Σ'} {A = A} m =
  fold {C = H (Abort + Σ') A} genH algH m (λ s → op (i₁ abort))

------------------------------------------------------------------------
-- Ligninger (Definition 2.1)

{-# NO_POSITIVITY_CHECK #-}
data Term {I : Set} (Σ : (I → I → Set₁) → (I → I → Set₁))
          (V : I → I → Set₁) : I → I → Set₁ where
  var : ∀ {i j} → V i j → Term Σ V i j
  opT : ∀ {i j} → Σ (Term Σ V) i j → Term Σ V i j

{-# TERMINATING #-}
foldT : ∀ {I} {Σ : (I → I → Set₁) → (I → I → Set₁)} {V C : I → I → Set₁}
          ⦃ _ : Functor Σ ⦄ {j : I}
      → (∀ {i} → V i j → C i j)
      → (∀ {i} → Σ C i j → C i j)
      → ∀ {i} → Term Σ V i j → C i j
foldT ρ alg (var v) = ρ v
foldT ρ alg (opT s) = alg (fmap (foldT ρ alg) s)

-- substitution: bind af et Free-program ind i en term med variable
{-# TERMINATING #-}
bindT : ∀ {I} {Σ : (I → I → Set₁) → (I → I → Set₁)} {V : I → I → Set₁}
          ⦃ _ : Functor Σ ⦄ {A : Set₁} {i k j : I}
      → Free Σ A i k → (A → Term Σ V k j) → Term Σ V i j
bindT (pure x) f = f x
bindT (op s)   f = opT (fmap (λ m → bindT m f) s)

infix 4 _≐_
data Equation {lΓ I} (Σ : (I → I → Set₁) → (I → I → Set₁))
              (Γ : Set lΓ) (V : I → I → Set₁) (i j : I) : Set (suc zero ⊔ lΓ) where
  _≐_ : (Γ → Term Σ V i j) → (Γ → Term Σ V i j) → Equation Σ Γ V i j

lhs rhs : ∀ {lΓ I} {Σ : (I → I → Set₁) → (I → I → Set₁)} {Γ : Set lΓ}
            {V : I → I → Set₁} {i j : I}
        → Equation Σ Γ V i j → Γ → Term Σ V i j
lhs (l ≐ r) = l
rhs (l ≐ r) = r

respects : ∀ {lΓ I} {Σ : (I → I → Set₁) → (I → I → Set₁)} {Γ : Set lΓ}
             {V C : I → I → Set₁} {i j : I} ⦃ _ : Functor Σ ⦄
         → (∀ {a} → Σ C a j → C a j)
         → Equation Σ Γ V i j → Set (suc zero ⊔ lΓ)
respects {V = V} {C = C} {j = j} alg eq =
  ∀ (ρ : ∀ {a} → V a j → C a j) t →
    foldT ρ alg (lhs eq t) ≡ foldT ρ alg (rhs eq t)


