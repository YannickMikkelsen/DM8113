module Slopp.StateSig where

-- Parameterized state-signatur i to-indeks-stilen. IKKE typechecket.
--
--   look : proj → M i i a                     (læser komponent a af indekset)
--   set  : inj → (val : a) → M i (inj i val) ⊤ (skriver komponent a)
--
-- ANTAGELSE (jeg har ikke set dine definitioner):
--   ProjL I a   = I → a
--   InjL I a J  = I → a → J

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Slopp.PHexc
open import Slopp.Lawful
open Functor ⦃...⦄

ProjL : Set → Set → Set
ProjL I a = I → a

InjL : Set → Set → Set → Set
InjL I a J = I → a → J

-- Én konstruktør pr. operation. K i j er fortsættelsen: den starter i
-- operationens post-indeks og slutter i j (programmets slutindeks).
data StateOp {I : Set} (K : I → I → Set₁) : I → I → Set₁ where
  look : ∀ {i j} {a : Set} (proj : ProjL I a)
       → (a → K i j) → StateOp K i j
  set  : ∀ {i j} {a : Set} (inj : InjL I a I) (val : a)
       → K (inj i val) j → StateOp K i j

fmapSt : ∀ {I} {X Y : I → I → Set₁} {j j'}
       → (∀ {i} → X i j → Y i j')
       → ∀ {i} → StateOp X i j → StateOp Y i j'
fmapSt f (look proj k)    = look proj (λ a → f (k a))
fmapSt f (set inj val k)  = set inj val (f k)

instance
  fState : ∀ {I} → Functor (StateOp {I})
  fState = record { fmap = fmapSt }

------------------------------------------------------------------------
-- Lawful (til Gen)

AllSt : ∀ {I} {X : I → I → Set₁} {i j}
      → (∀ {a} → X a j → Set₁) → StateOp X i j → Set₁
AllSt Q (look _ k)  = ∀ a → Q (k a)
AllSt Q (set _ _ k) = Q k

fmap-∘St : ∀ {I} {X Y Z : I → I → Set₁} {j j' j''}
           (g : ∀ {i} → Y i j' → Z i j'')
           (f : ∀ {i} → X i j → Y i j')
           {i} (x : StateOp X i j)
         → fmapSt {X = Y} {Y = Z} {j = j'} {j' = j''} g
             (fmapSt {X = X} {Y = Y} {j = j} {j' = j'} f x)
           ≡ fmapSt {X = X} {Y = Z} {j = j} {j' = j''} (λ {a} v → g (f v)) x
fmap-∘St g f (look _ k)  = refl
fmap-∘St g f (set _ _ k) = refl

all-congSt : ∀ {I} {X Y : I → I → Set₁} {j j'}
             (Q : ∀ {a} → X a j → Set₁)
             (h₁ h₂ : ∀ {i} → X i j → Y i j')
             {i} (x : StateOp X i j)
           → AllSt {X = X} {i} {j} Q x
           → (∀ {a} (v : X a j) → Q {a} v → h₁ {a} v ≡ h₂ {a} v)
           → fmapSt {X = X} {Y = Y} {j = j} {j' = j'} h₁ x
             ≡ fmapSt {X = X} {Y = Y} {j = j} {j' = j'} h₂ x
all-congSt Q h₁ h₂ (look proj k)   a c = cong (look proj) (funext (λ v → c (k v) (a v)))
all-congSt Q h₁ h₂ (set inj val k) a c = cong (set inj val) (c k a)

lawfulState : ∀ {I} → Lawful (StateOp {I})
lawfulState = record { All = AllSt ; fmap-∘ = fmap-∘St ; all-cong = all-congSt }