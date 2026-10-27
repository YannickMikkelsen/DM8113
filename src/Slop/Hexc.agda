module Slop.Hexc where

open import Data.Unit  using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; if_then_else_)
open import Level using (Level; _⊔_; suc; zero; Lift; lift; lower)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; trans)
open import Data.Product using (_×_; _,_)

postulate
  funext : ∀ {a b} {A : Set a} {B : A → Set b} {f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g

cong₃ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
        (f : A → B → C → D) {x y : A} {u v : B} {s t : C}
      → x ≡ y → u ≡ v → s ≡ t → f x u s ≡ f y v t
cong₃ f refl refl refl = refl

record ⊤₁ : Set₁ where
  constructor tt₁

-- Free Σ A = pure A | op (Σ (Free Σ A))
{-# NO_POSITIVITY_CHECK #-}
data Free {l : Level} (Σ : Set l → Set l) (A : Set l) : Set l where
  pure : A → Free Σ A
  op   : Σ (Free Σ A) → Free Σ A

record Functor {l : Level} (F : Set l → Set l) : Set (suc l) where
  field fmap : ∀ {X Y} → (X → Y) → F X → F Y
open Functor ⦃...⦄

{-# TERMINATING #-}
_>>=_ : ∀ {l : Level} {Σ : Set l → Set l} {A B : Set l} ⦃ _ : Functor Σ ⦄ → Free Σ A → (A → Free Σ B) → Free Σ B
pure x >>= k = k x
op f   >>= k = op (fmap (_>>= k) f)

-- (F + G)
data _+_ (F G : Set₁ → Set₁) (K : Set₁) : Set₁ where
  i₁ : F K → (F + G) K
  i₂ : G K → (F + G) K

data Fire (K : Set₁) : Set₁ where
  fire : K → Fire K


data Exc (J : Set → Set₁) (K : Set₁) : Set₁ where
  throw : Exc J K
  end   : {A : Set} → J A → A → Exc J K
  catch : {A : Set} → (J A → K) → K → (A → K) → Exc J K

-- end j x >>= k = end j x
instance
  fExc : ∀ {J} → Functor (Exc J)
  fExc = record { fmap = λ where
    f (throw)       → throw
    f (end j x)     → end j x
    f (catch b h k) → catch (λ j → f (b j)) (f h) (λ x → f (k x)) }


instance
  fFire : Functor Fire
  fFire = record { fmap = λ where f (fire k) → fire (f k) }


prog : ∀ {J} → Free (Exc J + Fire) ⊤₁
prog = op (i₁ (catch {A = ⊤}
                 (λ j → op (i₁ (end j tt)))
                 (op (i₂ (fire (pure tt₁))))
                 (λ _ → pure tt₁)))



JΣ : (Σ : Set₁ → Set₁) → (R : Set₁) → Set → Set₁
JΣ Σ R X = X → Free Σ (Maybe R)


-- {-# TERMINATING #-}
-- hexc : ∀ {Σ A} ⦃ _ : Functor Σ ⦄
--      → Free (Exc (JΣ Σ A) + Σ) A → Free Σ (Maybe A)
-- hexc (pure x) = pure (just x)
-- hexc (op (i₁ throw)) = pure nothing
-- hexc (op (i₁ (end j x))) = j x
-- hexc (op (i₁ (catch p h k))) = --er ikke rekdig for lige nu siger vi hvis k fajler kører vi h der er ikke rekdigt. det skal værer hvis p og kun p fejler kører vi h.
--   hexc (p (λ x → hexc (k x))) >>= λ where
--     (just a) → pure (just a)
--     nothing  → hexc h
-- hexc (op (i₂ x)) = op (fmap hexc x)



-- {-# TERMINATING #-}
-- go : ∀ {Σ A} ⦃ _ : Functor Σ ⦄
--    → Free (Exc (JΣ Σ A) + Σ) A → Free Σ (Maybe A) → Free Σ (Maybe A)
-- go (pure x)                hd = pure (just x)
-- go (op (i₁ throw))         hd = hd
-- go (op (i₁ (end j x)))     hd = j x
-- go (op (i₁ (catch p h k))) hd = go (p (λ x → go (k x) hd)) (go h hd)
-- go (op (i₂ x))             hd = op (fmap (λ m → go m hd) x)

-- hexc : ∀ {Σ A} ⦃ _ : Functor Σ ⦄
--      → Free (Exc (JΣ Σ A) + Σ) A → Free Σ (Maybe A)
-- hexc m = go m (pure nothing)

------------------------------------------------------------------------------------------------------------------------------------------------
-- Lave om til en algebra

{-# TERMINATING #-}
fold : ∀ {l : Level} {Σ : Set l → Set l} {A B : Set l} ⦃ _ : Functor Σ ⦄ → (A → B) → (Σ B → B) → Free Σ A → B
fold gen alg (pure x) = gen x
fold gen alg (op f)   = alg (fmap (fold gen alg) f)

-- Functor instans
instance
  f+ : ∀ {F G} ⦃ _ : Functor F ⦄ ⦃ _ : Functor G ⦄ → Functor (F + G)
  f+ = record { fmap = λ where
    f (i₁ x) → i₁ (fmap f x)
    f (i₂ y) → i₂ (fmap f y) }

-- Bærertypen
H : (Σ : Set₁ → Set₁) → Set₁ → Set₁
H Σ A = Free Σ (Maybe A) → Free Σ (Maybe A)

-- Algebraen
genH : ∀ {Σ A} → A → H Σ A
genH x = λ hd → pure (just x)

algH : ∀ {Σ A} ⦃ _ : Functor Σ ⦄ → (Exc (JΣ Σ A) + Σ) (H Σ A) → H Σ A
algH (i₁ throw)       = λ hd → hd
algH (i₁ (end j x))   = λ hd → j x
algH (i₁ (catch p h k)) = λ hd → p (λ x → k x hd) (h hd)
algH (i₂ x)           = λ hd → op (fmap (λ m → m hd) x)

hexc' : ∀ {Σ A} ⦃ _ : Functor Σ ⦄ → Free (Exc (JΣ Σ A) + Σ) A → Free Σ (Maybe A)
hexc' m = fold genH algH m (pure nothing)

 


infix 4 _≐_
data Equation {lΓ : Level} (Σ : Set₁ → Set₁) (Γ : Set lΓ) (V : Set₁) : Set (suc zero ⊔ lΓ) where
  _≐_ : (Γ → Free Σ V) → (Γ → Free Σ V) → Equation Σ Γ V

lhs rhs : ∀ {lΓ : Level} {Σ : Set₁ → Set₁} {Γ : Set lΓ} {V : Set₁} → Equation Σ Γ V → Γ → Free Σ V
lhs (l ≐ r) = l
rhs (l ≐ r) = r

-- Definition 2.1
respects : ∀ {lΓ : Level} {Σ : Set₁ → Set₁} {Γ : Set lΓ} {V C : Set₁} ⦃ _ : Functor Σ ⦄ → (Σ C → C) → Equation Σ Γ V → Set (suc zero ⊔ lΓ)
respects {V = V} {C = C} alg eq =
  ∀ (ρ : V → C) t → fold ρ alg (lhs eq t) ≡ fold ρ alg (rhs eq t)


data Opr (P : Set) (Ar : P → Set) (K : Set₁) : Set₁ where
  opr : (p : P) → (Ar p → K) → Opr P Ar K

instance
  fOpr : ∀ {P Ar} → Functor (Opr P Ar)
  fOpr = record { fmap = λ where f (opr p c) → opr p (λ b → f (c b)) }


module Eqs (P : Set) (Ar : P → Set) (A : Set₁) where
  Σ = Opr P Ar
  J = JΣ Σ A
  S = Exc J + Σ

  data CVar (X : Set) : Set₁ where
    hv : CVar X
    kv : X → CVar X

   -- catch (λ j → end j x) h k ≡ k x
  eq1 : (X : Set) → Equation S X (CVar X)
  eq1 X = (λ x → op (i₁ (catch (λ j → op (i₁ (end j x))) (pure hv) λ a → pure (kv a)))) ≐ (λ x → pure (kv x))

  eq1-ok : ∀ X → respects {C = H Σ A} algH (eq1 X)
  eq1-ok X ρ t = refl

  -- catch (λ j → throw) h k ≡ h
  eq2 : (X : Set) → Equation S ⊤ (CVar X)
  eq2 X = (λ x → op (i₁ (catch (λ j → op (i₁ throw)) (pure hv) λ a → pure (kv a)))) ≐ (λ x → pure hv)

  eq2-ok : ∀ X → respects {C = H Σ A} algH (eq2 X)
  eq2-ok X ρ t = refl


  module Bind (X : Set) (Y V : Set₁) where

    -- end j x >>= f ≡ end j x
    eq4 : Equation S (J X × X × (Y → Free S V)) V
    eq4 = (λ{ (j , x , f) → (op (i₁ (end j x))) >>= f }) ≐ (λ{ (j , x , f) → op (i₁ (end j x)) })

    eq4-ok : respects algH eq4
    eq4-ok ρ (j , x , f) = refl

    -- throw >>= f ≡ throw
    eq5 : Equation S (Y → Free S V) V
    eq5 = (λ f → (op (i₁ throw)) >>= f ) ≐ λ f → op (i₁ throw)

    eq5-ok : respects algH eq5
    eq5-ok ρ f = refl

    -- catch p h k >>= f ≡ catch (λ j → p j >>= f) (h >>= f) (λ a → k a >>= f)
    eq6 : Equation S ((J X → Free S Y) × Free S Y × (X → Free S Y) × (Y → Free S V)) V
    eq6 = (λ{ (p , h , k , f) → op (i₁ (catch p h k)) >>= f }) ≐ λ{ (p , h , k , f) → op (i₁ (catch (λ j → (p j) >>= f) (h >>= f) λ a → (k a) >>= f)) }

    eq6-ok : respects algH eq6
    eq6-ok ρ (p , h , k , f) = refl

    data NoPure {R : Set₁} : Free S R → Set₁ where   -- sluter altid på end eller throw
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
    np-bind : ∀ {R Z : Set₁} (g : Z → H Σ A) (f₁ f₂ : R → Free S Z) {q : Free S R}
            → NoPure q → fold g algH (q >>= f₁) ≡ fold g algH (q >>= f₂)
    np-bind g f₁ f₂ np-throw = refl
    np-bind g f₁ f₂ (np-end j y) = refl
    np-bind g f₁ f₂ (np-op c x ih) =
      cong (λ F → λ hd → op (opr c (λ b → F b hd)))
           (funext (λ b → np-bind g f₁ f₂ (ih b)))
    np-bind g f₁ f₂ (np-catch b h k nb nh nk) =
      cong₃ (λ B Hh K → λ hd → B (λ x → K x hd) (Hh hd))
            (funext (λ j → np-bind g f₁ f₂ (nb j)))
            (np-bind g f₁ f₂ nh)
            (funext (λ a → np-bind g f₁ f₂ (nk a)))

    main : ∀ (ρ : Y → H Σ A) (k : X → Free S Y) {p : Free S (Lift (suc zero) X)} → WF p → ∀ hd
         → fold ρ algH (p >>= λ { (lift x) → op (i₁ (end (λ a → fold ρ algH (k a) hd) x)) }) hd
           ≡ fold ρ algH (p >>= λ { (lift x) → k x }) hd
    main ρ k (wf-pure (lift y)) hd = refl
    main ρ k wf-throw          hd = refl
    main ρ k (wf-end j y)      hd = refl
    main ρ k (wf-op c x ih)    hd = cong (λ F → op (opr c F)) (funext (λ b → main ρ k (ih b) hd))
    main ρ k (wf-catch b h' k'' nb wh wk) hd =
      cong₃ (λ B Jv Hv → B Jv Hv)
            (funext (λ j → np-bind ρ
                (λ { (lift x) → op (i₁ (end (λ a → fold ρ algH (k a) hd) x)) })
                (λ { (lift x) → k x })
                (nb j)))
            (funext (λ a → main ρ k (wk a) hd))
            (main ρ k wh hd)

    eq3-ok : respects algH eq3
    eq3-ok ρ (wft p wf , k) = funext (λ hd → main ρ k wf hd)


  module Inter (p : P) (X : Set) (Y V : Set₁) where

    data MVar : Set₁ where
      hv : MVar
      kv : X → MVar
      mv : J X → Ar p → MVar

    -- catch (λ j → opr p (λ b → m j b)) h k
    --   ≡ opr p (λ b → catch (λ j → m j b) h k)

    eq7 : Equation S ⊤ MVar
    eq7 = (λ x → op (i₁ (catch (λ j → (op (i₂ (opr p (λ b → pure (mv j b)))))) (pure hv) λ a → pure (kv a)))) ≐ λ x → op (i₂ (opr p (λ b → op (i₁ (catch (λ j → pure (mv j b)) (pure hv) λ a → pure (kv a))))))


    eq7-ok : respects algH eq7
    eq7-ok ρ tt = refl
    -- throw >>= (λ _ → opr p f) ≡ throw
    eq8 : Equation S (Ar p → Free S V) V
    eq8 = (λ f → (op (i₁ throw)) >>= λ (_ : A) → op (i₂ (opr p f))) ≐ λ f → op (i₁ throw)

    eq8-ok : respects algH eq8
    eq8-ok ρ f = refl

  module Comm (P1 : Set) (Ar1 : P1 → Set)
            (P2 : Set) (Ar2 : P2 → Set)
            (_==_ : ∀ {p} → Ar1 p → Ar1 p → Bool)
            (p1 : P1) (p2 : P2) (b : Ar1 p1) where

    S2 = Opr P1 Ar1 + Opr P2 Ar2

    data KVar : Set₁ where
      k1 : Ar1 p1 → KVar
      k2 : Ar2 p2 → KVar

    eqComm : Equation S2 ⊤ KVar
    eqComm =
      (λ _ → op (i₁ (opr p1 (λ a1 →
              if a1 == b
              then op (i₂ (opr p2 (λ a2 → pure (k2 a2))))
              else pure (k1 a1)))))
      ≐
      (λ _ → op (i₂ (opr p2 (λ a2 →
              op (i₁ (opr p1 (λ a1 →
                if a1 == b then pure (k2 a2) else pure (k1 a1))))))))

    -- eqComm-ok : respects algH eqComm
    -- eqComm-ok = ?






------------- test

-- Skriv test her 

module Tests where

  J₀ = JΣ Fire ⊤₁
  S₀ = Exc J₀ + Fire
  T  = Free S₀ ⊤₁             
  R  = Free Fire (Maybe ⊤₁)    

  run : T → R
  run = hexc' {Σ = Fire} {A = ⊤₁}

  throw' : T
  throw' = op (i₁ throw)

  fire' : T → T
  fire' m = op (i₂ (fire m))

  end' : J₀ ⊤ → T
  end' j = op (i₁ (end j tt))

  catch' : (J₀ ⊤ → T) → T → (⊤ → T) → T
  catch' p h k = op (i₁ (catch {A = ⊤} p h k))

  ok : R
  ok = pure (just tt₁)

  fail : R
  fail = pure nothing

  fired : R → R
  fired r = op (fire r)

  t-pure : run (pure tt₁) ≡ ok
  t-pure = refl

  t-throw : run throw' ≡ fail
  t-throw = refl

  t-fire : run (fire' (pure tt₁)) ≡ fired ok
  t-fire = refl

  t-fire-throw : run (fire' throw') ≡ fired fail
  t-fire-throw = refl


  t-eq1 : run (catch' (λ j → end' j) (fire' (pure tt₁)) (λ _ → pure tt₁)) ≡ ok
  t-eq1 = refl

  t-eq2 : run (catch' (λ j → throw') (fire' (pure tt₁)) (λ _ → pure tt₁)) ≡ fired ok
  t-eq2 = refl

  t-k-fejler-ikke-h : run (catch' (λ j → end' j) (fire' (pure tt₁)) (λ _ → throw')) ≡ fail
  t-k-fejler-ikke-h = refl

  t-p-fejler-h : run (catch' (λ j → throw') (fire' (pure tt₁)) (λ _ → throw')) ≡ fired ok
  t-p-fejler-h = refl

  t-eq4 : run (catch' (λ j → end' j >>= λ _ → fire' (pure tt₁)) (pure tt₁) (λ _ → pure tt₁)) ≡ ok
  t-eq4 = refl

  t-eq5 : run (throw' >>= λ _ → fire' (pure tt₁)) ≡ fail
  t-eq5 = refl




  lhs3 : T → (⊤ → T) → T
  lhs3 m k = catch' (λ j → m >>= λ _ → end' j) throw' k

  rhs3 : T → (⊤ → T) → T
  rhs3 m k = m >>= λ _ → k tt

  m-fire : T
  m-fire = catch' (λ j → throw') (fire' (pure tt₁)) (λ _ → pure tt₁)

  m-end : T
  m-end = catch' (λ j → end' j) (fire' (pure tt₁)) (λ _ → pure tt₁)

  t-eq3-A : run (lhs3 (pure tt₁) (λ _ → throw')) ≡ fail
  t-eq3-A = refl
  t-eq3-A' : run (rhs3 (pure tt₁) (λ _ → throw')) ≡ fail
  t-eq3-A' = refl

  t-eq3-B : run (lhs3 throw' (λ _ → fire' (pure tt₁))) ≡ fail
  t-eq3-B = refl
  t-eq3-B' : run (rhs3 throw' (λ _ → fire' (pure tt₁))) ≡ fail
  t-eq3-B' = refl

  t-eq3-C : run (lhs3 m-fire (λ _ → throw')) ≡ fired fail
  t-eq3-C = refl
  t-eq3-C' : run (rhs3 m-fire (λ _ → throw')) ≡ fired fail
  t-eq3-C' = refl

  t-eq3-D : run (lhs3 m-fire (λ _ → fire' (pure tt₁))) ≡ fired (fired ok)
  t-eq3-D = refl
  t-eq3-D' : run (rhs3 m-fire (λ _ → fire' (pure tt₁))) ≡ fired (fired ok)
  t-eq3-D' = refl

  t-eq3-E : run (lhs3 m-end (λ _ → throw')) ≡ fail
  t-eq3-E = refl
  t-eq3-E' : run (rhs3 m-end (λ _ → throw')) ≡ fail
  t-eq3-E' = refl

  t-eq3-C=  : run (lhs3 m-fire (λ _ → throw')) ≡ run (rhs3 m-fire (λ _ → throw'))
  t-eq3-C=  = refl


  m-pure : T
  m-pure = catch' (λ j → pure tt₁) (fire' (pure tt₁)) (λ _ → pure tt₁)

  t-eq3-bad-lhs : run (lhs3 m-pure (λ _ → throw')) ≡ fail
  t-eq3-bad-lhs = refl

  t-eq3-bad-rhs : run (rhs3 m-pure (λ _ → throw')) ≡ fired fail
  t-eq3-bad-rhs = refl
