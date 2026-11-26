module Pmonad.FHAlg where

open import Data.Unit          using (⊤; tt)
open import Data.String        using (String)
open import Data.Product       using (_×_; _,_)
open import Level using (Lift; lift; zero; suc)
open import Relation.Binary.PropositionalEquality
  using (refl)
open import Pmonad.Hexc
  using (Opr; opr; Free; pure; op; Equation; _≐_; respects; fold; funext)

------------------------------------------------------------------------
-- 1. Signatur
--
-- Ingen pointers. Programmer er ren syntaks i `Free`, så dårlige
-- programmer (fopen uden fclose, write uden fopen) type-checker.

data FileOp : Set where
  fopenOp  : String → FileOp
  freadOp  : FileOp
  fwriteOp : String → FileOp
  fcloseOp : FileOp

-- Aritet = returtype
ArFile : FileOp → Set
ArFile (fopenOp _)  = ⊤
ArFile freadOp      = String
ArFile (fwriteOp _) = ⊤
ArFile fcloseOp     = ⊤

ΣFile : Set₁ → Set₁
ΣFile = Opr FileOp ArFile

------------------------------------------------------------------------
-- 2. Smart constructors

fopen : ∀ {A : Set₁} → String → (⊤ → Free ΣFile A) → Free ΣFile A
fopen path k = op (opr (fopenOp path) k)

fread : ∀ {A : Set₁} → (String → Free ΣFile A) → Free ΣFile A
fread k = op (opr freadOp k)

fwrite : ∀ {A : Set₁} → String → (⊤ → Free ΣFile A) → Free ΣFile A
fwrite s k = op (opr (fwriteOp s) k)

fclose : ∀ {A : Set₁} → (⊤ → Free ΣFile A) → Free ΣFile A
fclose k = op (opr fcloseOp k)

------------------------------------------------------------------------
-- 3. Semantik
--
-- Som State.agda: tilstanden er kun filens indhold. Der holdes INGEN
-- styr på, om filen er åben eller lukket, så fopen og fclose gør
-- ingenting ved tilstanden. Algebraen er total og har ingen grene.

HFile : Set₁ → Set₁
HFile R = String → R × String

genFile : ∀ {R : Set₁} → R → HFile R
genFile v m = v , m

algFile : ∀ {R : Set₁} → Opr FileOp ArFile (HFile R) → HFile R
algFile (opr (fopenOp _)  k) m = k tt m
algFile (opr (fwriteOp s) k) m = k tt s      -- overskriver
algFile (opr freadOp      k) m = k m  m
algFile (opr fcloseOp     k) m = k tt m

run : ∀ {V : Set₁} → Free ΣFile V → HFile V
run = fold genFile algFile

------------------------------------------------------------------------
-- 4. Love
--
-- Alle lovene gælder fra enhver starttilstand og er rigtige ligninger,
-- bevist med `respects` (Definition 2.1), ligesom state-lovene.

-- Variabeltypen er den, hver lov har brug for: ⊤ når der ikke er noget
-- hul med argument, og String når hullet får den læste streng.

module FileLaws (R : Set₁) where

  ⊤₁ : Set₁
  ⊤₁ = Lift (suc zero) ⊤

  String₁ : Set₁
  String₁ = Lift (suc zero) String

  -- fopen ; fclose ≡ pure
  eq-open-close : Equation ΣFile ⊤ ⊤₁
  eq-open-close =
    (λ _ → fopen "f" (λ _ → fclose (λ _ → pure (lift tt))))
    ≐ (λ _ → pure (lift tt))

  eq-open-close-ok : respects {C = HFile R} algFile eq-open-close
  eq-open-close-ok ρ tt = funext (λ m → refl)

  -- write s1 ; write s2 ≡ write s2
  eq-write-write : Equation ΣFile (String × String) ⊤₁
  eq-write-write =
    (λ{ (s1 , s2) → fwrite s1 (λ _ → fwrite s2 (λ _ → pure (lift tt))) })
    ≐ (λ{ (_ , s2) → fwrite s2 (λ _ → pure (lift tt)) })

  eq-write-write-ok : respects {C = HFile R} algFile eq-write-write
  eq-write-write-ok ρ (s1 , s2) = funext (λ m → refl)

  -- write s ; read ≡ write s ; pure s
  eq-write-read : Equation ΣFile String String₁
  eq-write-read =
    (λ s → fwrite s (λ _ → fread (λ r → pure (lift r))))
    ≐ (λ s → fwrite s (λ _ → pure (lift s)))

  eq-write-read-ok : respects {C = HFile R} algFile eq-write-read
  eq-write-read-ok ρ s = funext (λ m → refl)

  -- BEMÆRK: fopen ; write s ; fclose ≡ write s gælder også i modellen,
  -- men er ikke en ressourcelov. Den holder kun, fordi fopen og fclose
  -- ikke rører tilstanden, så write ikke kan se, om en fil er åben.
  -- Højresiden har en write uden fopen, altså et dårligt program.