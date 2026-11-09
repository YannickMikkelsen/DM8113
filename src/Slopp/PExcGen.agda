module Slopp.PExcGen where

open import Data.Unit using (⊤; tt)
open import Level using (suc; zero; Lift; lift)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Product using (_×_; _,_)
open import Slopp.PHexc
open import Slopp.Lawful
open Functor ⦃...⦄

-- Exc-ligningerne for algebraen algE, over signaturen Opr P Ar
-- module Gen (I : Set) (P : I → I → Set) (Ar : ∀ {i m} → P i m → Set)
--            (R : Set₁) (i₀ j₀ k₀ m₀ : I) where
--   Σ = Opr P Ar
--   J = JΣ Σ R j₀
--   S = Exc J + Σ
--   C = H Σ R

module Gen {I : Set}
           (Σ : (I → I → Set₁) → (I → I → Set₁)) ⦃ fΣ : Functor Σ ⦄
           (L : Lawful Σ)
           (i₀ j₀ k₀ m₀ : I)
           (D : I → I → Set₁)
           (αD : ∀ {a} → Σ D a j₀ → D a j₀) where

  open Lawful L

  -- hop fra tilstand k med en X ender i D k j₀
  J : I → Set → Set₁
  J k X = X → D k j₀

  S : (I → I → Set₁) → (I → I → Set₁)
  S = Exc J + Σ

  -- bærertype: "kør med en handler hd, der kan køres fra enhver fejltilstand"
  C : I → I → Set₁
  C i j = ((s : I) → D s j) → D i j

  -- Exc-delen er uændret; Σ-delen sendes videre til αD
  algE : ∀ {i} → S C i j₀ → C i j₀
  algE {i} (i₁ throw)         = λ hd → hd i
  algE (i₁ (end l x))         = λ hd → l x
  algE (i₁ (catch p h k))     = λ hd → p (λ x → k x hd) (λ s → h s hd)
  algE (i₂ x)                 = λ hd → αD (fmap (λ {a} m → m hd) x)

  -- Lovlighed af S = Exc J + Σ: Σ er givet, Exc J skal bevises
  postulate lawfulExc : Lawful (Exc J)   -- TODO: bevis (som for Fire, Abort, Opr)

  lawfulS : Lawful S
  lawfulS = lawful+ lawfulExc L

  -- beregningsvariable: h kaldes fra enhver s, k' starter i i₀ eller k₀
  data MV (X : Set) : I → I → Set₁ where
    hv : ∀ {s} → MV X s j₀
    kv : X → MV X i₀ j₀
    kw : X → MV X k₀ j₀

  ----------------------------------------------------------------------
  -- Catch-End: catch (λ ℓ → end ℓ x) h k' ≡ k' x

  eq-Catch-End : (X : Set) → Equation S X (MV X) i₀ j₀
  eq-Catch-End X = (λ x → opT (i₁ (catch {k = i₀}
                                (λ ℓ → opT (i₁ (end ℓ x)))
                                (λ s → var hv)
                                (λ a → var (kv a)))))
          ≐ (λ x → var (kv x))

  eq-Catch-End-ok : ∀ X → respects {Σ = S} {C = C} {j = j₀} algE (eq-Catch-End X)
  eq-Catch-End-ok X ρ x = refl

  ----------------------------------------------------------------------
  -- Catch-Throw: catch (λ _ → throw) h k' ≡ h

  eq-Catch-Throw : (X : Set) → Equation S ⊤ (MV X) i₀ j₀
  eq-Catch-Throw X = (λ _ → opT (i₁ (catch {k = k₀}
                                (λ _ → opT (i₁ throw))
                                (λ s → var hv)
                                (λ a → var (kw a)))))
          ≐ (λ _ → var hv)

  eq-Catch-Throw-ok : ∀ X → respects {Σ = S} {C = C} {j = j₀} algE (eq-Catch-Throw X)
  eq-Catch-Throw-ok X ρ tt = refl

  ----------------------------------------------------------------------
  -- End-Through: catch (λ _ → end ℓ x) h k' ≡ end ℓ x

  Γ₃ : Set → Set₁
  Γ₃ X = J i₀ X × X

  eq-end-through : (X : Set) → Equation S (Γ₃ X) (MV X) i₀ j₀
  eq-end-through X =
    (λ { (ℓ , x) → opT (i₁ (catch {k = k₀}
                                  (λ _ → opT (i₁ (end ℓ x)))
                                  (λ s → var hv)
                                  (λ a → var (kw a)))) })
    ≐ (λ { (ℓ , x) → opT (i₁ (end ℓ x)) })

  eq-end-through-ok : ∀ X → respects {Σ = S} {C = C} {j = j₀} algE (eq-end-through X)
  eq-end-through-ok X ρ (ℓ , x) = refl

  ----------------------------------------------------------------------
  -- Catch-Bind: catch (λ ℓ → p >>= λ x → end ℓ x) (λ s → throw) k' ≡ p >>= k'
  -- (ℓ ∉ p gælder automatisk: p er en værdi i Γ og ℓ er bundet inde i kroppen)

  eq3 : (X : Set) → Equation S (Free S (Lift (suc zero) X) i₀ k₀) (MV X) i₀ j₀
  eq3 X = (λ p →
              opT (i₁ (catch {k = k₀} {A = X}
                             (λ ℓ → bindT p (λ { (lift x) → opT (i₁ (end ℓ x)) }))
                             (λ s → opT (i₁ throw))
                             (λ a → var (kw a)))))
          ≐ (λ p → bindT p (λ { (lift x) → var (kw x) }))

  -- Bemærk: loven gælder ikke for alle p (jf. WF-eksemplet), så beviset er et hul.
  eq3-ok : ∀ X → respects {Σ = S} {C = C} {j = j₀} algE (eq3 X)
  eq3-ok X ρ p = {!!}

  ----------------------------------------------------------------------
  -- Bind-lovene. p, h, k er Free-termer i Γ; fortsættelsen f er variablen kw
  -- (f : B → M k₀ j₀ C), bundet ind med bindT.

  kT : (X : Set) → Lift (suc zero) X → Term S (MV X) k₀ j₀
  kT X (lift b) = var (kw b)

  -- End-Bind: end ℓ x >>= f ≡ end ℓ x
  Γ₄ : Set → Set₁
  Γ₄ W = J i₀ W × W

  eq-Bind-lovene : (X W : Set) → Equation S (Γ₄ W) (MV X) i₀ j₀
  eq-Bind-lovene X W = (λ { (ℓ , x) → bindT (op (i₁ (end ℓ x))) (kT X) })
            ≐ (λ { (ℓ , x) → opT (i₁ (end ℓ x)) })

  eq-Bind-lovene-ok : ∀ X W → respects {Σ = S} {C = C} {j = j₀} algE (eq-Bind-lovene X W)
  eq-Bind-lovene-ok X W ρ (ℓ , x) = refl

  -- Throw-Bind: throw >>= f ≡ throw
  eq-Throw-Bind : (X : Set) → Equation S ⊤ (MV X) i₀ j₀
  eq-Throw-Bind X = (λ _ → bindT (op (i₁ throw)) (kT X))
          ≐ (λ _ → opT (i₁ throw))

  eq-Throw-Bind-ok : ∀ X → respects {Σ = S} {C = C} {j = j₀} algE (eq-Throw-Bind X)
  eq-Throw-Bind-ok X ρ tt = refl

  -- Catch-Distr: catch p h k >>= f ≡ catch (λ ℓ → p ℓ >>= f) (λ s → h s >>= f) (λ a → k a >>= f)
  Γ₆ : Set → Set → Set₁
  Γ₆ X W = (J m₀ W → Free S (Lift (suc zero) X) i₀ k₀)
         × ((s : I) → Free S (Lift (suc zero) X) s k₀)
         × (W → Free S (Lift (suc zero) X) m₀ k₀)

  eq-Catch-Distr : (X W : Set) → Equation S (Γ₆ X W) (MV X) i₀ j₀
  eq-Catch-Distr X W = (λ { (p , h , k) → bindT (op (i₁ (catch {A = W} p h k))) (kT X) })
            ≐ (λ { (p , h , k) →
                  opT (i₁ (catch {k = m₀} {A = W}
                                 (λ ℓ → bindT (p ℓ) (kT X))
                                 (λ s → bindT (h s) (kT X))
                                 (λ a → bindT (k a) (kT X)))) })

  eq-Catch-Distr-ok : ∀ X W → respects {Σ = S} {C = C} {j = j₀} algE (eq-Catch-Distr X W)
  eq-Catch-Distr-ok X W ρ (p , h , k) = refl





  Natural : (B : Set) (n : I)
          → (∀ {K : I → I → Set₁} {j} → (B → K n j) → Σ K i₀ j) → Set₂
  Natural B n o =
    ∀ {K L : I → I → Set₁} {j}
      (f : ∀ {a} → K a j → L a j) (c : B → K n j)
    → fmap {X = K} {Y = L} {j = j} {j' = j} f (o {K} {j} c)
      ≡ o {L} {j} (λ b → f {n} (c b))
 
  module Inter (B : Set) (n₀ : I)
               (o : ∀ {K : I → I → Set₁} {j} → (B → K n₀ j) → Σ K i₀ j)
               (nat : Natural B n₀ o)
               (X : Set) where
 
    -- beregningsvariable: h (fra enhver s), k' (fra m₀), m ℓ b (fra n₀), f b (fra n₀)
    data MVar : I → I → Set₁ where
      hh : ∀ {s} → MVar s j₀
      kk : X → MVar m₀ j₀
      mm : J m₀ X → B → MVar n₀ j₀
      ff : B → MVar n₀ j₀
 
    -- Catch-Op: catch (λ ℓ → o (λ b → m ℓ b)) h k' ≡ o (λ b → catch (λ ℓ → m ℓ b) h k')
    eq-Catch-Op : Equation S ⊤ MVar i₀ j₀
    eq-Catch-Op = (λ _ → opT (i₁ (catch {k = m₀} {A = X}
                               (λ ℓ → opT (i₂ (o (λ b → var (mm ℓ b)))))
                               (λ s → var hh)
                               (λ a → var (kk a)))))
          ≐ (λ _ → opT (i₂ (o (λ b → opT (i₁ (catch {i = n₀} {k = m₀} {A = X}
                                                   (λ ℓ → var (mm ℓ b))
                                                   (λ s → var hh)
                                                   (λ a → var (kk a))))))))
 
    -- kræver nat (to gange, under funext over hd)
    eq-Catch-Op-ok : respects {Σ = S} {C = C} {j = j₀} algE eq-Catch-Op
    eq-Catch-Op-ok ρ tt = {!!}
 
    -- Throw-Op: throw >>= (λ _ → o f) ≡ throw
    eq-Throw-Op : Equation S ⊤ MVar i₀ j₀
    eq-Throw-Op = (λ _ → bindT (op (i₁ throw))
                       (λ (_ : Lift (suc zero) X) → opT (i₂ (o (λ b → var (ff b))))))
          ≐ (λ _ → opT (i₁ throw))
 
    eq-Throw-Op-ok : respects {Σ = S} {C = C} {j = j₀} algE eq-Throw-Op
    eq-Throw-Op-ok ρ tt = refl
 
    -- End-Op: end ℓ x >>= (λ _ → o f) ≡ end ℓ x
    Γ₉ : Set → Set₁
    Γ₉ W = J i₀ W × W
 
    eq-End-Op : (W : Set) → Equation S (Γ₉ W) MVar i₀ j₀
    eq-End-Op W = (λ { (ℓ , x) → bindT (op (i₁ (end ℓ x)))
                                 (λ (_ : Lift (suc zero) X) → opT (i₂ (o (λ b → var (ff b))))) })
            ≐ (λ { (ℓ , x) → opT (i₁ (end ℓ x)) })
 
    eq-End-Op-ok : ∀ W → respects {Σ = S} {C = C} {j = j₀} algE (eq-End-Op W)
    eq-End-Op-ok W ρ (ℓ , x) = refl
  -- TODO: Inter og Comm tages senere.