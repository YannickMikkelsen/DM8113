module Slop2.CombinedFile where

open import Data.Unit          using (⊤; tt)
open import Data.Maybe         using (Maybe; just; nothing)
open import Data.String        using (String)
open import Data.Product       using (_×_; _,_)
open import Data.Nat           using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Slop2.Hexc
open import Slop2.Lawful
open import Slop2.Ops
open import Slop2.FHAlg using (HFile; algFile)
open import Slop2.ExcGen
open Functor ⦃...⦄

module FileAlg (S : Set) (A : Set₁) where

  -- i₁ = Exc, i₂ (i₁ _) = state, i₂ (i₂ _) = fil
  Σ₀ : Set₁ → Set₁
  Σ₀ = StateOp S + FileOpS

  R : Set₁
  R = Maybe A × S

  D : Set₁
  D = S → HFile R

  αD : Σ₀ D → D
  αD (i₁ (get k))      = λ s → k s s
  αD (i₁ (put s' k))   = λ _ → k s'
  αD (i₂ (fopen p k))  = λ s → algFile (fopen p (k s))
  αD (i₂ (fread k))    = λ s → algFile (fread (λ r → k r s))
  αD (i₂ (fwrite w k)) = λ s → algFile (fwrite w (k s))
  αD (i₂ (fclose k))   = λ s → algFile (fclose (k s))

  Lw : Lawful Σ₀
  Lw = lawful+ lawful-St lawful-F

  module G = Gen Σ₀ Lw D αD

  Full : Set₁ → Set₁
  Full = G.S

  C : Set₁
  C = G.C

  algD : Full C → C
  algD = G.algE

  -- variable-type til lovene
  data TV : Set₁ where
    tv  : TV
    kv  : S → TV
    kv2 : S → S → TV
    kr  : String → TV
    kvr : S → String → TV

  ----------------------------------------------------------------------
  -- Exception-lovene eq1–eq9

  module ExcLaws (X : Set) (Y V : Set₁) where

    eq1-ok = G.eq1-ok X
    eq2-ok = G.eq2-ok X

    open G.Bind X Y V public          -- eq3–eq6 (+ eq3-ok for WF-termer)

    module IGet            = G.Inter S (λ k → i₁ (get k))              (λ f k → refl) X Y V
    module IPut (s : S)    = G.Inter ⊤ (λ k → i₁ (put s (k tt)))       (λ f k → refl) X Y V
    module IFopen (p : String) = G.Inter ⊤ (λ k → i₂ (fopen p (k tt))) (λ f k → refl) X Y V
    module IFread          = G.Inter String (λ k → i₂ (fread k))       (λ f k → refl) X Y V
    module IFwrite (w : String) = G.Inter ⊤ (λ k → i₂ (fwrite w (k tt))) (λ f k → refl) X Y V
    module IFclose         = G.Inter ⊤ (λ k → i₂ (fclose (k tt)))      (λ f k → refl) X Y V

  ----------------------------------------------------------------------
  -- State-lovene

  eqGQ : Equation Full ⊤ TV
  eqGQ = (λ _ → op (i₂ (i₁ (get (λ _ → pure tv)))))
       ≐ (λ _ → pure tv)

  eqPG : Equation Full S TV
  eqPG = (λ s → op (i₂ (i₁ (put s (op (i₂ (i₁ (get (λ s' → pure (kv s'))))))))))
       ≐ (λ s → op (i₂ (i₁ (put s (pure (kv s))))))

  eqGP : Equation Full ⊤ TV
  eqGP = (λ _ → op (i₂ (i₁ (get (λ s → op (i₂ (i₁ (put s (pure tv)))))))))
       ≐ (λ _ → pure tv)

  eqGG : Equation Full ⊤ TV
  eqGG = (λ _ → op (i₂ (i₁ (get (λ s → op (i₂ (i₁ (get (λ s' → pure (kv2 s s'))))))))))
       ≐ (λ _ → op (i₂ (i₁ (get (λ s → pure (kv2 s s))))))

  eqPP : Equation Full (S × S) TV
  eqPP = (λ{ (s1 , s2) → op (i₂ (i₁ (put s1 (op (i₂ (i₁ (put s2 (pure tv))))))))})
       ≐ (λ{ (_ , s2) → op (i₂ (i₁ (put s2 (pure tv)))) })

  eqGQ-ok : respects {C = C} algD eqGQ
  eqGQ-ok ρ tt = refl
  eqPG-ok : respects {C = C} algD eqPG
  eqPG-ok ρ s = refl
  eqGP-ok : respects {C = C} algD eqGP
  eqGP-ok ρ tt = refl
  eqGG-ok : respects {C = C} algD eqGG
  eqGG-ok ρ tt = refl
  eqPP-ok : respects {C = C} algD eqPP
  eqPP-ok ρ (s1 , s2) = refl

  ----------------------------------------------------------------------
  -- Fil-lovene

  -- fopen p ; fclose ≡ pure     (for ALLE stier p)
  eq-open-close : Equation Full String TV
  eq-open-close = (λ p → op (i₂ (i₂ (fopen p (op (i₂ (i₂ (fclose (pure tv)))))))))
                ≐ (λ _ → pure tv)

  eq-write-write : Equation Full (String × String) TV
  eq-write-write = (λ{ (s1 , s2) → op (i₂ (i₂ (fwrite s1 (op (i₂ (i₂ (fwrite s2 (pure tv)))))))) })
                 ≐ (λ{ (_ , s2) → op (i₂ (i₂ (fwrite s2 (pure tv)))) })

  eq-write-read : Equation Full String TV
  eq-write-read = (λ s → op (i₂ (i₂ (fwrite s (op (i₂ (i₂ (fread (λ r → pure (kr r))))))))))
                ≐ (λ s → op (i₂ (i₂ (fwrite s (pure (kr s))))))

  eq-open-close-ok : respects {C = C} algD eq-open-close
  eq-open-close-ok ρ p = refl
  eq-write-write-ok : respects {C = C} algD eq-write-write
  eq-write-write-ok ρ (s1 , s2) = refl
  eq-write-read-ok : respects {C = C} algD eq-write-read
  eq-write-read-ok ρ s = refl

  ----------------------------------------------------------------------
  -- Tensorlove: get/put kan skubbes forbi fil-operationer

  eq-get-fopen : Equation Full String TV
  eq-get-fopen =
    (λ p → op (i₂ (i₁ (get (λ s → op (i₂ (i₂ (fopen p (pure (kv s))))))))))
    ≐ (λ p → op (i₂ (i₂ (fopen p (op (i₂ (i₁ (get (λ s → pure (kv s))))))))))

  eq-get-fread : Equation Full ⊤ TV
  eq-get-fread =
    (λ _ → op (i₂ (i₁ (get (λ s → op (i₂ (i₂ (fread (λ r → pure (kvr s r))))))))))
    ≐ (λ _ → op (i₂ (i₂ (fread (λ r → op (i₂ (i₁ (get (λ s → pure (kvr s r))))))))))

  eq-get-fwrite : Equation Full String TV
  eq-get-fwrite =
    (λ w → op (i₂ (i₁ (get (λ s → op (i₂ (i₂ (fwrite w (pure (kv s))))))))))
    ≐ (λ w → op (i₂ (i₂ (fwrite w (op (i₂ (i₁ (get (λ s → pure (kv s))))))))))

  eq-get-fclose : Equation Full ⊤ TV
  eq-get-fclose =
    (λ _ → op (i₂ (i₁ (get (λ s → op (i₂ (i₂ (fclose (pure (kv s))))))))))
    ≐ (λ _ → op (i₂ (i₂ (fclose (op (i₂ (i₁ (get (λ s → pure (kv s))))))))))

  eq-put-fopen : Equation Full (String × S) TV
  eq-put-fopen =
    (λ{ (p , s') → op (i₂ (i₁ (put s' (op (i₂ (i₂ (fopen p (pure tv))))))))})
    ≐ (λ{ (p , s') → op (i₂ (i₂ (fopen p (op (i₂ (i₁ (put s' (pure tv)))))))) })

  eq-put-fread : Equation Full S TV
  eq-put-fread =
    (λ s' → op (i₂ (i₁ (put s' (op (i₂ (i₂ (fread (λ r → pure (kr r))))))))))
    ≐ (λ s' → op (i₂ (i₂ (fread (λ r → op (i₂ (i₁ (put s' (pure (kr r))))))))))

  eq-put-fwrite : Equation Full (String × S) TV
  eq-put-fwrite =
    (λ{ (w , s') → op (i₂ (i₁ (put s' (op (i₂ (i₂ (fwrite w (pure tv))))))))})
    ≐ (λ{ (w , s') → op (i₂ (i₂ (fwrite w (op (i₂ (i₁ (put s' (pure tv)))))))) })

  eq-put-fclose : Equation Full S TV
  eq-put-fclose =
    (λ s' → op (i₂ (i₁ (put s' (op (i₂ (i₂ (fclose (pure tv)))))))))
    ≐ (λ s' → op (i₂ (i₂ (fclose (op (i₂ (i₁ (put s' (pure tv)))))))))

  eq-get-fopen-ok : respects {C = C} algD eq-get-fopen
  eq-get-fopen-ok ρ p = refl
  eq-get-fread-ok : respects {C = C} algD eq-get-fread
  eq-get-fread-ok ρ tt = refl
  eq-get-fwrite-ok : respects {C = C} algD eq-get-fwrite
  eq-get-fwrite-ok ρ w = refl
  eq-get-fclose-ok : respects {C = C} algD eq-get-fclose
  eq-get-fclose-ok ρ tt = refl
  eq-put-fopen-ok : respects {C = C} algD eq-put-fopen
  eq-put-fopen-ok ρ (p , s') = refl
  eq-put-fread-ok : respects {C = C} algD eq-put-fread
  eq-put-fread-ok ρ s' = refl
  eq-put-fwrite-ok : respects {C = C} algD eq-put-fwrite
  eq-put-fwrite-ok ρ (w , s') = refl
  eq-put-fclose-ok : respects {C = C} algD eq-put-fclose
  eq-put-fclose-ok ρ s' = refl

------------------------------------------------------------------------------

module FileExample where
  open FileAlg ℕ ⊤₁          -- S = ℕ, A = ⊤₁

  genF : ⊤₁ → C
  genF x = λ hd s m → (just x , s) , m

  runD : Free Full ⊤₁ → D
  runD t = fold genF algD t (λ s m → (nothing , s) , m)

  -- leak: kroppen kaster, handleren (pure) lukker ikke filen
  leak : Free Full ⊤₁
  leak =
    op (i₂ (i₂ (fopen "f"
      ((op (i₁ (catch {A = ⊤}
          (λ j → op (i₂ (i₂ (fwrite "x" (op (i₁ throw))))))
          (pure tt₁)
          (λ _ → op (i₂ (i₂ (fclose (pure tt₁))))))))
       >>= λ _ →
         op (i₂ (i₂ (fopen "f"
           (op (i₂ (i₂ (fwrite "hello"
             (op (i₂ (i₂ (fclose (pure tt₁))))))))))))))))

  -- good: kroppen afsluttes med end, fortsættelsen lukker filen
  good : Free Full ⊤₁
  good =
    op (i₂ (i₂ (fopen "f"
      ((op (i₁ (catch {A = ⊤}
          (λ j → op (i₂ (i₂ (fwrite "x" (op (i₁ (end j tt)))))))
          (pure tt₁)
          (λ _ → op (i₂ (i₂ (fclose (pure tt₁))))))))
       >>= λ _ →
         op (i₂ (i₂ (fopen "f"
           (op (i₂ (i₂ (fwrite "hello"
             (op (i₂ (i₂ (fclose (pure tt₁))))))))))))))))

  test-leak : runD leak 0 "init" ≡ ((just tt₁ , 0) , "hello")
  test-leak = refl

  test-good : runD good 0 "init" ≡ ((just tt₁ , 0) , "hello")
  test-good = refl