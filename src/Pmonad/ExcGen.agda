module Pmonad.ExcGen where


open import Data.Unit using (⊤; tt)
open import Level using (suc; zero; Lift; lift)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Product using (_×_; _,_)
open import Pmonad.Hexc
open Functor ⦃...⦄

module Gen (P : Set) (Ar : P → Set) (D : Set₁) (αD : Opr P Ar D → D) where

  Σ : Set₁ → Set₁
  Σ = Opr P Ar

  J : Set → Set₁
  J X = X → D

  S : Set₁ → Set₁
  S = Exc J + Σ

  -- bærertypen: "kør med en given handler-fortsættelse hd"
  C : Set₁
  C = D → D

  -- Exc-algebraen. Alt andet (i₂) sendes videre til αD.
  algE : S C → C
  algE (i₁ throw)         = λ hd → hd
  algE (i₁ (end j x))     = λ hd → j x
  algE (i₁ (catch p h k)) = λ hd → p (λ x → k x hd) (h hd)
  algE (i₂ x)             = λ hd → αD (fmap (λ m → m hd) x)

  ----------------------------------------------------------------------
  -- eq1, eq2

  data CVar (X : Set) : Set₁ where
    hv : CVar X
    kv : X → CVar X

  -- catch (λ j → end j x) h k ≡ k x
  eq1 : (X : Set) → Equation S X (CVar X)
  eq1 X = (λ x → op (i₁ (catch (λ j → op (i₁ (end j x))) (pure hv) λ a → pure (kv a))))
          ≐ (λ x → pure (kv x))

  eq1-ok : ∀ X → respects {C = C} algE (eq1 X)
  eq1-ok X ρ t = refl

  -- catch (λ j → throw) h k ≡ h
  eq2 : (X : Set) → Equation S ⊤ (CVar X)
  eq2 X = (λ x → op (i₁ (catch (λ j → op (i₁ throw)) (pure hv) λ a → pure (kv a))))
          ≐ (λ x → pure hv)

  eq2-ok : ∀ X → respects {C = C} algE (eq2 X)
  eq2-ok X ρ t = refl

  ----------------------------------------------------------------------
  -- eq3 - eq6  (bind)

  module Bind (X : Set) (Y V : Set₁) where

    -- end j x >>= f ≡ end j x
    eq4 : Equation S (J X × X × (Y → Free S V)) V
    eq4 = (λ{ (j , x , f) → (op (i₁ (end j x))) >>= f })
          ≐ (λ{ (j , x , f) → op (i₁ (end j x)) })

    eq4-ok : respects {C = C} algE eq4
    eq4-ok ρ (j , x , f) = refl

    -- throw >>= f ≡ throw
    eq5 : Equation S (Y → Free S V) V
    eq5 = (λ f → (op (i₁ throw)) >>= f) ≐ λ f → op (i₁ throw)

    eq5-ok : respects {C = C} algE eq5
    eq5-ok ρ f = refl

    -- catch p h k >>= f ≡ catch (λ j → p j >>= f) (h >>= f) (λ a → k a >>= f)
    eq6 : Equation S ((J X → Free S Y) × Free S Y × (X → Free S Y) × (Y → Free S V)) V
    eq6 = (λ{ (p , h , k , f) → op (i₁ (catch p h k)) >>= f })
          ≐ λ{ (p , h , k , f) → op (i₁ (catch (λ j → (p j) >>= f) (h >>= f) λ a → (k a) >>= f)) }

    eq6-ok : respects {C = C} algE eq6
    eq6-ok ρ (p , h , k , f) = refl

    eq-end : Equation S (J X × X × Free S Y × (X → Free S Y)) Y
    eq-end = (λ{ (i , x , h , k) → op (i₁ (catch (λ j → op (i₁ (end i x))) h k)) })
             ≐ (λ{ (i , x , h , k) → op (i₁ (end i x)) })

    eq-end-ok : respects {C = C} algE eq-end
    eq-end-ok ρ (i , x , h , k) = refl

    data NoPure {R : Set₁} : Free S R → Set₁ where   -- slutter altid på end eller throw
      np-throw : NoPure (op (i₁ throw))
      np-end   : ∀ {W} (j : J W) (y : W) → NoPure (op (i₁ (end j y)))
      np-op    : ∀ c (x : Ar c → Free S R) → (∀ a → NoPure (x a))
               → NoPure (op (i₂ (opr c x)))
      np-catch : ∀ {W} (p : J W → Free S R) (h : Free S R) (k : W → Free S R)
               → (∀ j → NoPure (p j)) → NoPure h → (∀ a → NoPure (k a))
               → NoPure (op (i₁ (catch p h k)))

    data WF {R : Set₁} : Free S R → Set₁ where
      wf-pure  : ∀ y → WF (pure y)
      wf-throw : WF (op (i₁ throw))
      wf-end   : ∀ {W} (j : J W) (y : W) → WF (op (i₁ (end j y)))
      wf-op    : ∀ c (x : Ar c → Free S R) → (∀ a → WF (x a))
               → WF (op (i₂ (opr c x)))
      wf-catch : ∀ {W} (p : J W → Free S R) (h : Free S R) (k : W → Free S R)
               → (∀ j → NoPure (p j)) → WF h → (∀ a → WF (k a))
               → WF (op (i₁ (catch p h k)))

    record WFTerm : Set₁ where
      constructor wft
      field
        term : Free S (Lift (suc zero) X)
        wf   : WF term

    -- catch (λ j → p >>= end j) throw k ≡ p >>= k    (p veldannet)
    eq3 : Equation S (WFTerm × (X → Free S Y)) Y
    eq3 = (λ{ (wft p _ , k) → op (i₁ (catch {A = X}
                                         (λ j → p >>= λ {(lift x) → op (i₁ (end j x)) })
                                         (op (i₁ throw))
                                         k)) })
          ≐ (λ{ (wft p _ , k) → p >>= λ { (lift x) → k x} })

    -- NoPure-led: k kører aldrig i kroppen, så det er ligegyldigt hvad vi binder med
    np-bind : ∀ {R Z : Set₁} (g : Z → C) (f₁ f₂ : R → Free S Z) {q : Free S R}
            → NoPure q → fold g algE (q >>= f₁) ≡ fold g algE (q >>= f₂)
    np-bind g f₁ f₂ np-throw = refl
    np-bind g f₁ f₂ (np-end j y) = refl
    np-bind g f₁ f₂ (np-op c x ih) =
      cong (λ (F : Ar c → C) → λ hd → αD (opr c (λ b → F b hd)))
           (funext (λ b → np-bind g f₁ f₂ (ih b)))
    np-bind g f₁ f₂ (np-catch b h k nb nh nk) =
      cong₃ (λ B Hh K → λ hd → B (λ x → K x hd) (Hh hd))
            (funext (λ j → np-bind g f₁ f₂ (nb j)))
            (np-bind g f₁ f₂ nh)
            (funext (λ a → np-bind g f₁ f₂ (nk a)))

    main : ∀ (ρ : Y → C) (k : X → Free S Y) {p : Free S (Lift (suc zero) X)} → WF p → ∀ hd
         → fold ρ algE (p >>= λ { (lift x) → op (i₁ (end (λ a → fold ρ algE (k a) hd) x)) }) hd
           ≡ fold ρ algE (p >>= λ { (lift x) → k x }) hd
    main ρ k (wf-pure (lift y)) hd = refl
    main ρ k wf-throw          hd = refl
    main ρ k (wf-end j y)      hd = refl
    main ρ k (wf-op c x ih)    hd =
      cong (λ (F : Ar c → D) → αD (opr c F)) (funext (λ b → main ρ k (ih b) hd))
    main ρ k (wf-catch b h' k'' nb wh wk) hd =
      cong₃ (λ B Jv Hv → B Jv Hv)
            (funext (λ j → np-bind ρ
                (λ { (lift x) → op (i₁ (end (λ a → fold ρ algE (k a) hd) x)) })
                (λ { (lift x) → k x })
                (nb j)))
            (funext (λ a → main ρ k (wk a) hd))
            (main ρ k wh hd)

    eq3-ok : respects {C = C} algE eq3
    eq3-ok ρ (wft p wf , k) = funext (λ hd → main ρ k wf hd)



  -- eq7, eq8  (interaktion med en vilkårlig operation p)

  module Inter (p : P) (X : Set) (Y V : Set₁) where

    data MVar : Set₁ where
      hv : MVar
      kv : X → MVar
      mv : J X → Ar p → MVar

    -- catch (λ j → opr p (λ b → m j b)) h k ≡ opr p (λ b → catch (λ j → m j b) h k)
    eq7 : Equation S ⊤ MVar
    eq7 = (λ x → op (i₁ (catch (λ j → op (i₂ (opr p (λ b → pure (mv j b))))) (pure hv) λ a → pure (kv a))))
          ≐ λ x → op (i₂ (opr p (λ b → op (i₁ (catch (λ j → pure (mv j b)) (pure hv) λ a → pure (kv a))))))

    eq7-ok : respects {C = C} algE eq7
    eq7-ok ρ tt = refl

    -- throw >>= (λ _ → opr p f) ≡ throw
    eq8 : Equation S (Ar p → Free S V) V
    eq8 = (λ f → (op (i₁ throw)) >>= λ (_ : Y) → op (i₂ (opr p f))) ≐ λ f → op (i₁ throw)

    eq8-ok : respects {C = C} algE eq8
    eq8-ok ρ f = refl