module IndexedMonad.Definition where
open import Data.Unit    using (⊤; tt)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.Char using (Char)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Function using (_∘_)
open import Data.String  using (String)

record IxMonad {I : Set} {M : I → I → Set → Set} : Set₁ where
  field
    pure : ∀ {i} {A : Set} → A → M i i A
    _>>=_ : ∀ {i j k} {A B : Set} → M i j A → (A → M j k B) → M i k B


Pred : Set → Set₁
Pred I = I → Set

 
_:→_ : ∀ {I : Set} → (Pred I) → (Pred I) → Set
s :→ t = ∀ {i} → s i → t i


record _:>>:_ {I : Set} (P Q : Pred I) (R : Pred I) (i : I) : Set where
  constructor _:&_
  field
    pi : P i
    k  : Q :→ R
infixr 4 _:&_
infixr 3 _:+:_
data _:+:_ {I : Set} (F G : Pred I → Pred I) (P : Pred I) (i : I) : Set where
  InL : F P i → (F :+: G) P i 
  InR : G P i → (F :+: G) P i 

idP : ∀ {I} {P : Pred I} → P :→ P
idP {P} {i} x = x

composeP : ∀ {I} {P Q R : Pred I} → (Q :→ R) → (P :→ Q) → (P :→ R)
composeP g f {i} x = g (f x)


record IFunctor {I : Set} (F : Pred I → Pred I) : Set₁ where
  field
    imap    : ∀ {s t} → (s :→ t) → ((F s) :→ (F t))
    -- imap-id : ∀ {P : Pred I} {i : I} (x : F P i)
    --         → imap {P} {P} idP x ≡ x
    -- imap-∘  : ∀ {P Q R : Pred I} (g : Q :→ R) (f : P :→ Q) {i : I} (x : F P i)
    --         → imap {Q} {R} g (imap {P} {Q} f x) ≡ imap {P} {R} (composeP g f) x


open IFunctor public
open _:>>:_ public
instance0 : ∀ {I : Set} {P Q : Pred I} → IFunctor (P :>>: Q)
instance0 .imap = λ z {i} z₁ → z₁ .pi :& (λ {i = i₁} z₂ → z (z₁ .k z₂))


open IFunctor public
instance1 : ∀ {I : Set} {F G : Pred I → Pred I}
      → IFunctor F → IFunctor G → IFunctor (F :+: G)
instance1 FI GI .imap h (InL fp) = InL (FI .imap h fp)
instance1 FI GI .imap h (InR gp) = InR (GI .imap h gp)

data _:=_ {X : Set} (A : Set) (k : X) : X → Set where
  V : A → (A := k) k

{-# NO_POSITIVITY_CHECK #-}
data :∗ {I : Set} (F : Pred I → Pred I) (P : Pred I) (i : I) : Set where
  Ret : P i → :∗ F P i
  Do  : F (:∗ F P) i → :∗ F P i


record IMonad {I : Set} (M : Pred I → Pred I) : Set₁ where
  field
    iskip      : ∀ {P : Pred I} → P :→ M P
    iextend    : ∀ {P Q : Pred I} → (P :→ M Q) → (M P :→ M Q)

open IMonad public
open IFunctor public

{-# TERMINATING #-}
instance3 : ∀ {I : Set} {F : Pred I → Pred I} → IFunctor F → IMonad (:∗ F)
instance3 x .iskip = Ret
instance3 x .iextend x₁ (Ret x₂) = x₁ x₂
instance3 x .iextend g (Do ffp) = Do (x .imap (iextend (instance3 x) g) ffp)

{-# TERMINATING #-}
instance4 : ∀ {I : Set} {F : Pred I → Pred I} → IFunctor F → IFunctor (:∗ F)
instance4 x .imap h (Ret p)  = Ret (h p)
instance4 x .imap h (Do ffp)  =  Do (x .imap (instance4 x .imap h) ffp)


