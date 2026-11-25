module Slopp.FHAlg where

open import Data.String  using (String)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Slopp.PHexc
open import Slopp.Lawful
open Functor ⦃...⦄



data FStatus : Set where
  Open Closed : FStatus

data SFile : FStatus → Set where
  SOpen   : SFile Open
  SClosed : SFile Closed

ProjF : Set → Set
ProjF I = I → FStatus

InjF : Set → FStatus → Set → Set
InjF I s J = I → SFile s → J


data FileOpS {I : Set} (K : I → I → Set₁) : I → I → Set₁ where
  fopen  : ∀ {i j} (getOC : ProjF I) → getOC i ≡ Closed
         → (inj : InjF I Open I) → String
         → K (inj i SOpen) j → FileOpS K i j
  fread  : ∀ {i j} (getOC : ProjF I) → getOC i ≡ Open
         → (String → K i j) → FileOpS K i j
  fwrite : ∀ {i j} (getOC : ProjF I) → getOC i ≡ Open
         → String → K i j → FileOpS K i j
  fclose : ∀ {i j} (getOC : ProjF I) → getOC i ≡ Open
         → (inj : InjF I Closed I)
         → K (inj i SClosed) j → FileOpS K i j

fmapFile : ∀ {I} {X Y : I → I → Set₁} {j j'}
         → (∀ {i} → X i j → Y i j')
         → ∀ {i} → FileOpS X i j → FileOpS Y i j'
fmapFile f (fopen g p inj s k)  = fopen g p inj s (f k)
fmapFile f (fread g p k)        = fread g p (λ s → f (k s))
fmapFile f (fwrite g p s k)     = fwrite g p s (f k)
fmapFile f (fclose g p inj k)   = fclose g p inj (f k)

instance
  fFile : ∀ {I} → Functor (FileOpS {I})
  fFile = record { fmap = fmapFile }

HF : ∀ {I : Set} → Set₁ → I → I → Set₁
HF R _ _ = String → R × String

algFile : ∀ {I : Set} {R : Set₁} {i j : I} → FileOpS (HF {I} R) i j → HF {I} R i j
algFile (fopen _ _ _ _ k) m = k m
algFile (fread _ _ k)     m = k m m
algFile (fwrite _ _ s k)  m = k s          -- overskriver
algFile (fclose _ _ _ k)  m = k m


AllFile : ∀ {I} {X : I → I → Set₁} {i j}
        → (∀ {a} → X a j → Set₁) → FileOpS X i j → Set₁
AllFile Q (fopen _ _ _ _ k) = Q k
AllFile Q (fread _ _ k)     = ∀ s → Q (k s)
AllFile Q (fwrite _ _ _ k)  = Q k
AllFile Q (fclose _ _ _ k)  = Q k

fmap-∘File : ∀ {I} {X Y Z : I → I → Set₁} {j j' j''}
             (g : ∀ {i} → Y i j' → Z i j'')
             (f : ∀ {i} → X i j → Y i j')
             {i} (x : FileOpS X i j)
           → fmapFile {X = Y} {Y = Z} {j = j'} {j' = j''} g
               (fmapFile {X = X} {Y = Y} {j = j} {j' = j'} f x)
             ≡ fmapFile {X = X} {Y = Z} {j = j} {j' = j''} (λ {a} v → g (f v)) x
fmap-∘File g f (fopen _ _ _ _ k) = refl
fmap-∘File g f (fread _ _ k)     = refl
fmap-∘File g f (fwrite _ _ _ k)  = refl
fmap-∘File g f (fclose _ _ _ k)  = refl

all-congFile : ∀ {I} {X Y : I → I → Set₁} {j j'}
               (Q : ∀ {a} → X a j → Set₁)
               (h₁ h₂ : ∀ {i} → X i j → Y i j')
               {i} (x : FileOpS X i j)
             → AllFile {X = X} {i} {j} Q x
             → (∀ {a} (v : X a j) → Q {a} v → h₁ {a} v ≡ h₂ {a} v)
             → fmapFile {X = X} {Y = Y} {j = j} {j' = j'} h₁ x
               ≡ fmapFile {X = X} {Y = Y} {j = j} {j' = j'} h₂ x
all-congFile Q h₁ h₂ (fopen g p inj s k) a c = cong (fopen g p inj s) (c k a)
all-congFile Q h₁ h₂ (fread g p k)       a c = cong (fread g p) (funext (λ s → c (k s) (a s)))
all-congFile Q h₁ h₂ (fwrite g p s k)    a c = cong (fwrite g p s) (c k a)
all-congFile Q h₁ h₂ (fclose g p inj k)  a c = cong (fclose g p inj) (c k a)

lawfulFile : ∀ {I} → Lawful (FileOpS {I})
lawfulFile = record { All = AllFile ; fmap-∘ = fmap-∘File ; all-cong = all-congFile }