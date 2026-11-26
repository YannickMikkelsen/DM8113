module Pmonad.FreePmonad where
open import Agda.Primitive using (Setω)
open import Level using (Level; suc; zero; _⊔_)
open import Data.Unit    using (⊤; tt)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.Char using (Char)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Function using (_∘_)
open import Data.String  using (String; uncons; _++_; fromChar)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Pmonad.Pmonad-m2

open Combined combinedState





data Op (I : Set₁) : I → I → Set → Set₁ where
  Look   : ∀ {i} {A : Set} → (proj : ProjL I A) → Op I i i A
  SetOp  : ∀ {i} {A : Set} → (inj : InjL I A I) (val : A) → Op I i (inj i val) ⊤
  Fopen  : ∀ {i} → (getOC : ProjF I) → getOC i ≡ Closed → (inj : InjF I Open I) → String → Op I i (inj i SOpen) FH
  Fread  : ∀ {i} → (getOC : ProjF I) → getOC i ≡ Open → FH → Op I i i (Maybe Char)
  Fwrite : ∀ {i} → (getOC : ProjF I) → getOC i ≡ Open → FH → Char → Op I i i FH
  Fclose : ∀ {i} → (getOC : ProjF I) → getOC i ≡ Open → (inj : InjF I Closed I) → Op I i (inj i SClosed) ⊤
  Throw  : ∀ {i} {A : Set} → (inj : InjL I Flag I) → Op I i (inj i Unhandled) A


data Free (I : Set₁) (A : Set) : I → I → Set₁ where
  pureF  : ∀ {i} → A → Free I A i i
  impF   : ∀ {i j k} {B : Set} → Op I i k B → (B → Free I A k j) → Free I A i j
  catchF : ∀ {i k} → Free I A i k → (reset : InjC I I) → Free I A (reset i) (reset k) → Free I A i (reset k)


interpretOp : ∀ {i j A} → Op State i j A → M i j A
interpretOp (Look proj)             = look proj
interpretOp (SetOp inj val)         = set inj val
interpretOp (Fopen getOC eq inj fh) = fopen getOC eq inj fh
interpretOp (Fread getOC eq fh)     = fread getOC eq fh
interpretOp (Fwrite getOC eq fh c)  = fwrite getOC eq fh c
interpretOp (Fclose getOC eq inj)   = fclose getOC eq inj
interpretOp (Throw inj)             = throw inj

run : ∀ {A i j} → Free State A i j → M i j A
run (pureF x)          = pmonadState .PMonad.pure x
run (impF op k)        = interpretOp op >>>= (λ b → run (k b))
run (catchF t reset h) = catch (run t) reset (run h)







