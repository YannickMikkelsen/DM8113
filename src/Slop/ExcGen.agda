module Slop.ExcGen where

open import Data.Unit using (⊤; tt)
open import Level using (suc; zero; Lift; lift)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)
open import Data.Product using (_×_; _,_)
open import Slop.Hexc
open import Slop.Lawful
open Functor ⦃...⦄

-- Gen er nu parametriseret over en vilkårlig funktor Σ (ikke Opr P Ar)
module Gen (Σ : Set₁ → Set₁) ⦃ fΣ : Functor Σ ⦄ (L : Lawful Σ)
           (D : Set₁) (αD : Σ D → D) where

  open Lawful L

  J : Set → Set₁
  J X = X → D

  S : Set₁ → Set₁
  S = Exc J + Σ

  -- bærertypen: "kør med en given handler-fortsættelse hd"
  C : Set₁
  C = D → D

  -- Exc-algebraen (uændret). Alt andet (i₂) sendes videre til αD.
  algE : S C → C
  algE (i₁ throw)         = λ hd → hd
  algE (i₁ (end j x))     = λ hd → j x
  algE (i₁ (catch p h k)) = λ hd → p (λ x → k x hd) (h hd)
  algE (i₂ x)             = λ hd → αD (fmap (λ m → m hd) x)

  ----------------------------------------------------------------------
  -- eq1, eq2 (uændret)

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
  -- Hjælpelemmaer

  -- fold gennem en Σ-operation (erstatter den gamle definitionelle udfoldning)
  fold-op₂ : ∀ {R Z : Set₁} (g : Z → C) (f : R → Free S Z) (x : Σ (Free S R)) (hd : D)
           → fold g algE (op (i₂ x) >>= f) hd
           ≡ αD (fmap (λ a → fold g algE (a >>= f) hd) x)
  fold-op₂ g f x hd = cong αD
    (trans (fmap-∘ (λ (m : C) → m hd) (fold g algE) (fmap (λ a → a >>= f) x))
           (fmap-∘ (λ b → fold g algE b hd) (λ a → a >>= f) x))

  -- En "operationsform" o : (B → K) → Σ K er pladsholderen for en vilkårlig
  -- operation. Den skal være naturlig i K (refl for hver konkret operation).
  Natural : (B : Set) → (∀ {K : Set₁} → (B → K) → Σ K) → Set₂
  Natural B o = ∀ {K L : Set₁} (f : K → L) (c : B → K)
              → fmap f (o c) ≡ o (λ b → f (c b))

  module Op (B : Set) (o : ∀ {K : Set₁} → (B → K) → Σ K) (nat : Natural B o) where

    fold-o : ∀ {Z : Set₁} (g : Z → C) (c : B → Free S Z) (hd : D)
           → fold g algE (op (i₂ (o c))) hd ≡ αD (o (λ b → fold g algE (c b) hd))
    fold-o g c hd =
      cong αD (trans (cong (fmap (λ (m : C) → m hd)) (nat (fold g algE) c))
                     (nat (λ (m : C) → m hd) (λ b → fold g algE (c b))))

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

    -- NoPure/WF: np-op/wf-op er erstattet af "alle børn opfylder Q" via All
    {-# NO_POSITIVITY_CHECK #-}
    data NoPure {R : Set₁} : Free S R → Set₁ where
      np-throw : NoPure (op (i₁ throw))
      np-end   : ∀ {W} (j : J W) (y : W) → NoPure (op (i₁ (end j y)))
      np-op    : (x : Σ (Free S R)) → All NoPure x → NoPure (op (i₂ x))
      np-catch : ∀ {W} (p : J W → Free S R) (h : Free S R) (k : W → Free S R)
               → (∀ j → NoPure (p j)) → NoPure h → (∀ a → NoPure (k a))
               → NoPure (op (i₁ (catch p h k)))

    {-# NO_POSITIVITY_CHECK #-}
    data WF {R : Set₁} : Free S R → Set₁ where
      wf-pure  : ∀ y → WF (pure y)
      wf-throw : WF (op (i₁ throw))
      wf-end   : ∀ {W} (j : J W) (y : W) → WF (op (i₁ (end j y)))
      wf-op    : (x : Σ (Free S R)) → All WF x → WF (op (i₂ x))
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

    {-# TERMINATING #-}
    np-bind : ∀ {R Z : Set₁} (g : Z → C) (f₁ f₂ : R → Free S Z) {q : Free S R}
            → NoPure q → fold g algE (q >>= f₁) ≡ fold g algE (q >>= f₂)
    np-bind g f₁ f₂ np-throw = refl
    np-bind g f₁ f₂ (np-end j y) = refl
    np-bind g f₁ f₂ (np-op x nx) =
      funext (λ hd →
        trans (fold-op₂ g f₁ x hd)
        (trans (cong αD (all-cong NoPure
                          (λ a → fold g algE (a >>= f₁) hd)
                          (λ a → fold g algE (a >>= f₂) hd)
                          x nx
                          (λ a na → cong (λ (F : C) → F hd) (np-bind g f₁ f₂ na))))
               (sym (fold-op₂ g f₂ x hd))))
    np-bind g f₁ f₂ (np-catch b h k nb nh nk) =
      cong₃ (λ B Hh K → λ hd → B (λ x → K x hd) (Hh hd))
            (funext (λ j → np-bind g f₁ f₂ (nb j)))
            (np-bind g f₁ f₂ nh)
            (funext (λ a → np-bind g f₁ f₂ (nk a)))


    {-# TERMINATING #-}
    main : ∀ (ρ : Y → C) (k : X → Free S Y) {p : Free S (Lift (suc zero) X)} → WF p → ∀ hd
         → fold ρ algE (p >>= λ { (lift x) → op (i₁ (end (λ a → fold ρ algE (k a) hd) x)) }) hd
           ≡ fold ρ algE (p >>= λ { (lift x) → k x }) hd
    main ρ k (wf-pure (lift y)) hd = refl
    main ρ k wf-throw          hd = refl
    main ρ k (wf-end j y)      hd = refl
    main ρ k (wf-op x wx)      hd =
      trans (fold-op₂ ρ f₁ x hd)
      (trans (cong αD (all-cong WF
                        (λ a → fold ρ algE (a >>= f₁) hd)
                        (λ a → fold ρ algE (a >>= f₂) hd)
                        x wx
                        (λ a wa → main ρ k wa hd)))
             (sym (fold-op₂ ρ f₂ x hd)))
      where
        f₁ : Lift (suc zero) X → Free S Y
        f₁ (lift x') = op (i₁ (end (λ a → fold ρ algE (k a) hd) x'))
        f₂ : Lift (suc zero) X → Free S Y
        f₂ (lift x') = k x'
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

  ----------------------------------------------------------------------
  -- eq7 - eq9: catch kan skubbes ind under en VILKÅRLIG operation o

  module Inter (B : Set) (o : ∀ {K : Set₁} → (B → K) → Σ K) (nat : Natural B o)
               (X : Set) (Y V : Set₁) where

    open Op B o nat

    data MVar : Set₁ where
      hv : MVar
      kv : X → MVar
      mv : J X → B → MVar

    -- catch (λ j → o (λ b → m j b)) h k ≡ o (λ b → catch (λ j → m j b) h k)
    eq7 : Equation S ⊤ MVar
    eq7 = (λ _ → op (i₁ (catch {A = X}
                           (λ j → op (i₂ (o (λ b → pure (mv j b)))))
                           (pure hv)
                           (λ a → pure (kv a)))))
          ≐ (λ _ → op (i₂ (o (λ b → op (i₁ (catch {A = X}
                                              (λ j → pure (mv j b))
                                              (pure hv)
                                              (λ a → pure (kv a))))))))

    eq7-ok : respects {C = C} algE eq7
    eq7-ok ρ tt = funext (λ hd →
      trans (fold-o ρ (λ b → pure (mv (λ x → ρ (kv x) hd) b)) (ρ hv hd))
            (sym (fold-o ρ (λ b → op (i₁ (catch {A = X}
                                            (λ j → pure (mv j b))
                                            (pure hv)
                                            (λ a → pure (kv a))))) hd)))

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

  ----------------------------------------------------------------------
  -- Tensor: to operationer o₁, o₂ kommuterer, hvis algebraen gør (commD)

  module Comm (B₁ B₂ : Set)
              (o₁ : ∀ {K : Set₁} → (B₁ → K) → Σ K) (n₁ : Natural B₁ o₁)
              (o₂ : ∀ {K : Set₁} → (B₂ → K) → Σ K) (n₂ : Natural B₂ o₂)
              (commD : ∀ (u : B₁ → B₂ → D)
                     → αD (o₁ (λ a₁ → αD (o₂ (λ a₂ → u a₁ a₂))))
                     ≡ αD (o₂ (λ a₂ → αD (o₁ (λ a₁ → u a₁ a₂))))) where

    open Op B₁ o₁ n₁ renaming (fold-o to fold-o₁)
    open Op B₂ o₂ n₂ renaming (fold-o to fold-o₂)

    data KVar : Set₁ where
      kk : B₁ → B₂ → KVar

    -- o₁ (λ a₁ → o₂ (λ a₂ → k a₁ a₂)) ≡ o₂ (λ a₂ → o₁ (λ a₁ → k a₁ a₂))
    eqComm : Equation S ⊤ KVar
    eqComm = (λ _ → op (i₂ (o₁ (λ a₁ → op (i₂ (o₂ (λ a₂ → pure (kk a₁ a₂))))))))
             ≐ (λ _ → op (i₂ (o₂ (λ a₂ → op (i₂ (o₁ (λ a₁ → pure (kk a₁ a₂))))))))

    eqComm-ok : respects {C = C} algE eqComm
    eqComm-ok ρ tt = funext (λ hd →
      trans (fold-o₁ ρ (λ a₁ → op (i₂ (o₂ (λ a₂ → pure (kk a₁ a₂))))) hd)
      (trans (cong (λ u → αD (o₁ u))
                   (funext (λ a₁ → fold-o₂ ρ (λ a₂ → pure (kk a₁ a₂)) hd)))
      (trans (commD (λ a₁ a₂ → ρ (kk a₁ a₂) hd))
      (trans (cong (λ u → αD (o₂ u))
                   (funext (λ a₂ → sym (fold-o₁ ρ (λ a₁ → pure (kk a₁ a₂)) hd))))
             (sym (fold-o₂ ρ (λ a₂ → op (i₂ (o₁ (λ a₁ → pure (kk a₁ a₂))))) hd))))))