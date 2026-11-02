module Slop2.ExcGen where

open import Data.Unit using (⊤; tt)
open import Level using (suc; zero; Lift; lift)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)
open import Data.Product using (_×_; _,_)
open import Slop2.Hexc
open import Slop2.Lawful
open Functor ⦃...⦄

module Gen (Σ : Set₁ → Set₁) ⦃ FΣ : Functor Σ ⦄ (L : Lawful Σ)
           (D : Set₁) (αD : Σ D → D) where

  open Lawful L

  J : Set → Set₁
  J X = X → D

  S : Set₁ → Set₁
  S = Exc J + Σ

  C : Set₁
  C = D → D

  -- Exc-algebraen er uændret; alt i₂ sendes videre til αD
  algE : S C → C
  algE (i₁ throw)         = λ hd → hd
  algE (i₁ (end j x))     = λ hd → j x
  algE (i₁ (catch p h k)) = λ hd → p (λ x → k x hd) (h hd)
  algE (i₂ x)             = λ hd → αD (fmap (λ m → m hd) x)

  -- hjælpelemma: tre fmap'er samles til én
  fmap3 : ∀ {X Y Z W : Set₁} (a : Z → W) (b : Y → Z) (c : X → Y) (x : Σ X)
        → fmap a (fmap b (fmap c x)) ≡ fmap (λ t → a (b (c t))) x
  fmap3 a b c x =
    trans (cong (fmap a) (sym (fmap-∘ b c x)))
          (sym (fmap-∘ a (λ t → b (c t)) x))

  ----------------------------------------------------------------------
  -- eq1, eq2

  data CVar (X : Set) : Set₁ where
    hv : CVar X
    kv : X → CVar X

  eq1 : (X : Set) → Equation S X (CVar X)
  eq1 X = (λ x → op (i₁ (catch (λ j → op (i₁ (end j x))) (pure hv) λ a → pure (kv a))))
          ≐ (λ x → pure (kv x))

  eq1-ok : ∀ X → respects {C = C} algE (eq1 X)
  eq1-ok X ρ t = refl

  eq2 : (X : Set) → Equation S ⊤ (CVar X)
  eq2 X = (λ x → op (i₁ (catch (λ j → op (i₁ throw)) (pure hv) λ a → pure (kv a))))
          ≐ (λ x → pure hv)

  eq2-ok : ∀ X → respects {C = C} algE (eq2 X)
  eq2-ok X ρ t = refl

  ----------------------------------------------------------------------
  -- eq3 - eq6  (bind)

  module Bind (X : Set) (Y V : Set₁) where

    eq4 : Equation S (J X × X × (Y → Free S V)) V
    eq4 = (λ{ (j , x , f) → (op (i₁ (end j x))) >>= f })
          ≐ (λ{ (j , x , f) → op (i₁ (end j x)) })

    eq4-ok : respects {C = C} algE eq4
    eq4-ok ρ (j , x , f) = refl

    eq5 : Equation S (Y → Free S V) V
    eq5 = (λ f → (op (i₁ throw)) >>= f) ≐ λ f → op (i₁ throw)

    eq5-ok : respects {C = C} algE eq5
    eq5-ok ρ f = refl

    eq6 : Equation S ((J X → Free S Y) × Free S Y × (X → Free S Y) × (Y → Free S V)) V
    eq6 = (λ{ (p , h , k , f) → op (i₁ (catch p h k)) >>= f })
          ≐ λ{ (p , h , k , f) → op (i₁ (catch (λ j → (p j) >>= f) (h >>= f) λ a → (k a) >>= f)) }

    eq6-ok : respects {C = C} algE eq6
    eq6-ok ρ (p , h , k , f) = refl

    -- slutter altid på end eller throw
    {-# NO_POSITIVITY_CHECK #-}
    data NoPure {R : Set₁} : Free S R → Set₁ where
      np-throw : NoPure (op (i₁ throw))
      np-end   : ∀ {W} (j : J W) (y : W) → NoPure (op (i₁ (end j y)))
      np-op    : (x : Σ (Free S R)) → All (NoPure {R}) x → NoPure (op (i₂ x))
      np-catch : ∀ {W} (p : J W → Free S R) (h : Free S R) (k : W → Free S R)
               → (∀ j → NoPure (p j)) → NoPure h → (∀ a → NoPure (k a))
               → NoPure (op (i₁ (catch p h k)))

    {-# NO_POSITIVITY_CHECK #-}
    data WF {R : Set₁} : Free S R → Set₁ where
      wf-pure  : ∀ y → WF (pure y)
      wf-throw : WF (op (i₁ throw))
      wf-end   : ∀ {W} (j : J W) (y : W) → WF (op (i₁ (end j y)))
      wf-op    : (x : Σ (Free S R)) → All (WF {R}) x → WF (op (i₂ x))
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

    -- de to fortsættelser i beviset
    e1 : (ρ : Y → C) (k : X → Free S Y) (hd : D) → Lift (suc zero) X → Free S Y
    e1 ρ k hd (lift x) = op (i₁ (end (λ a → fold ρ algE (k a) hd) x))

    e2 : (k : X → Free S Y) → Lift (suc zero) X → Free S Y
    e2 k (lift x) = k x

    -- NoPure-led: k kører aldrig i kroppen, så det er ligegyldigt hvad vi binder med
    {-# TERMINATING #-}
    np-bind : ∀ {R Z : Set₁} (g : Z → C) (f₁ f₂ : R → Free S Z) {q : Free S R}
            → NoPure q → fold g algE (q >>= f₁) ≡ fold g algE (q >>= f₂)
    np-bind g f₁ f₂ np-throw = refl
    np-bind g f₁ f₂ (np-end j y) = refl
    np-bind g f₁ f₂ (np-op x al) =
      funext (λ hd → cong αD
        (trans (fmap3 (λ m → m hd) (fold g algE) (λ t → t >>= f₁) x)
        (trans (all-ext al
                  (λ t → fold g algE (t >>= f₁) hd)
                  (λ t → fold g algE (t >>= f₂) hd)
                  (λ t n → cong (λ m → m hd) (np-bind g f₁ f₂ n)))
               (sym (fmap3 (λ m → m hd) (fold g algE) (λ t → t >>= f₂) x)))))
    np-bind g f₁ f₂ (np-catch b h k nb nh nk) =
      cong₃ (λ B Hh K → λ hd → B (λ x → K x hd) (Hh hd))
            (funext (λ j → np-bind g f₁ f₂ (nb j)))
            (np-bind g f₁ f₂ nh)
            (funext (λ a → np-bind g f₁ f₂ (nk a)))

    {-# TERMINATING #-}
    main : ∀ (ρ : Y → C) (k : X → Free S Y) {p : Free S (Lift (suc zero) X)} → WF p → ∀ hd
         → fold ρ algE (p >>= e1 ρ k hd) hd ≡ fold ρ algE (p >>= e2 k) hd
    main ρ k (wf-pure (lift y)) hd = refl
    main ρ k wf-throw           hd = refl
    main ρ k (wf-end j y)       hd = refl
    main ρ k (wf-op x al)       hd =
      cong αD
        (trans (fmap3 (λ m → m hd) (fold ρ algE) (λ t → t >>= e1 ρ k hd) x)
        (trans (all-ext al
                  (λ t → fold ρ algE (t >>= e1 ρ k hd) hd)
                  (λ t → fold ρ algE (t >>= e2 k) hd)
                  (λ t w → main ρ k w hd))
               (sym (fmap3 (λ m → m hd) (fold ρ algE) (λ t → t >>= e2 k) x))))
    main ρ k (wf-catch b h' k'' nb wh wk) hd =
      cong₃ (λ B Jv Hv → B Jv Hv)
            (funext (λ j → np-bind ρ (e1 ρ k hd) (e2 k) (nb j)))
            (funext (λ a → main ρ k (wk a) hd))
            (main ρ k wh hd)

    eq3-ok : respects {C = C} algE eq3
    eq3-ok ρ (wft p wf , k) = funext (λ hd → main ρ k wf hd)

  ----------------------------------------------------------------------
  -- eq7 - eq9: interaktion med en vilkårlig operation o
  --   o er pladsholder for "en operation med aritet B":
  --   o k = get k, put s (k tt), fopen p (k tt), fread k, ...

  module Inter (B : Set)
               (o : ∀ {K : Set₁} → (B → K) → Σ K)
               (nat : ∀ {K L : Set₁} (f : K → L) (k : B → K)
                    → fmap f (o k) ≡ o (λ b → f (k b)))
               (X : Set) (Y V : Set₁) where

    data MVar : Set₁ where
      hv : MVar
      kv : X → MVar
      mv : J X → B → MVar

    -- catch (λ j → o (λ b → m j b)) h k ≡ o (λ b → catch (λ j → m j b) h k)
    eq7 : Equation S ⊤ MVar
    eq7 = (λ x → op (i₁ (catch (λ j → op (i₂ (o (λ b → pure (mv j b))))) (pure hv) λ a → pure (kv a))))
          ≐ λ x → op (i₂ (o (λ b → op (i₁ (catch (λ j → pure (mv j b)) (pure hv) λ a → pure (kv a))))))

    lem : ∀ {K L M : Set₁} (f : K → L) (g : L → M) (k : B → K)
        → fmap g (fmap f (o k)) ≡ o (λ b → g (f (k b)))
    lem f g k = trans (cong (λ u → fmap g u) (nat f k)) (nat g (λ b → f (k b)))

    eq7-ok : respects {C = C} algE eq7
    eq7-ok ρ tt = funext (λ hd →
      trans (cong αD (lem (fold ρ algE) (λ m → m (ρ hv hd))
                          (λ b → pure (mv (λ a → ρ (kv a) hd) b))))
            (sym (cong αD (lem (fold ρ algE) (λ m → m hd)
                          (λ b → op (i₁ (catch {A = X} (λ j → pure (mv j b))
                                                (pure hv) (λ a → pure (kv a)))))))))

    -- throw >>= (λ _ → o f) ≡ throw
    eq8 : Equation S (B → Free S V) V
    eq8 = (λ f → (op (i₁ throw)) >>= λ (_ : Y) → op (i₂ (o f))) ≐ λ f → op (i₁ throw)

    eq8-ok : respects {C = C} algE eq8
    eq8-ok ρ f = refl

    -- end j x >>= (λ _ → o f) ≡ end j x
    eq9 : Equation S (J X × X × (B → Free S V)) V
    eq9 = (λ{ (j , x , f) → (op (i₁ (end j x))) >>= λ (_ : Y) → op (i₂ (o f)) })
          ≐ (λ{ (j , x , f) → op (i₁ (end j x)) })

    eq9-ok : respects {C = C} algE eq9
    eq9-ok ρ (j , x , f) = refl