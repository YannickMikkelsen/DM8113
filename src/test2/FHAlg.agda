module Slop2.FHAlg where

open import Data.Unit          using (⊤; tt)
open import Data.String        using (String)
open import Data.Product       using (_×_; _,_)
open import Level using (Lift; lift; zero; suc)
open import Relation.Binary.PropositionalEquality using (refl)
open import Slop2.Hexc
  using (Free; pure; op; Equation; _≐_; respects; fold; funext)
open import Slop2.Ops

-- Semantik: tilstanden er kun filens indhold; fopen/fclose rører den ikke.
HFile : Set₁ → Set₁
HFile R = String → R × String

genFile : ∀ {R : Set₁} → R → HFile R
genFile v m = v , m

algFile : ∀ {R : Set₁} → FileOpS (HFile R) → HFile R
algFile (fopen _ k)  m = k m
algFile (fwrite s k) m = k s        -- overskriver
algFile (fread k)    m = k m m
algFile (fclose k)   m = k m

run : ∀ {V : Set₁} → Free FileOpS V → HFile V
run = fold genFile algFile

module FileLaws (R : Set₁) where

  ⊤₁ : Set₁
  ⊤₁ = Lift (suc zero) ⊤

  String₁ : Set₁
  String₁ = Lift (suc zero) String

  -- fopen p ; fclose ≡ pure     (for ALLE stier p)
  eq-open-close : Equation FileOpS String ⊤₁
  eq-open-close =
    (λ p → op (fopen p (op (fclose (pure (lift tt))))))
    ≐ (λ _ → pure (lift tt))

  eq-open-close-ok : respects {C = HFile R} algFile eq-open-close
  eq-open-close-ok ρ p = funext (λ m → refl)

  -- write s1 ; write s2 ≡ write s2
  eq-write-write : Equation FileOpS (String × String) ⊤₁
  eq-write-write =
    (λ{ (s1 , s2) → op (fwrite s1 (op (fwrite s2 (pure (lift tt))))) })
    ≐ (λ{ (_ , s2) → op (fwrite s2 (pure (lift tt))) })

  eq-write-write-ok : respects {C = HFile R} algFile eq-write-write
  eq-write-write-ok ρ (s1 , s2) = funext (λ m → refl)

  -- write s ; read ≡ write s ; pure s
  eq-write-read : Equation FileOpS String String₁
  eq-write-read =
    (λ s → op (fwrite s (op (fread (λ r → pure (lift r))))))
    ≐ (λ s → op (fwrite s (pure (lift s))))

  eq-write-read-ok : respects {C = HFile R} algFile eq-write-read
  eq-write-read-ok ρ s = funext (λ m → refl)