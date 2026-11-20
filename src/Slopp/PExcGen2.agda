module Slopp.PExcGen2 where

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Level using (suc; zero; Lift; lift)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Data.Product using (_×_; _,_)
open import Slopp.PHexc2
open import Slopp.Lawful
open import Slopp.PEquivComp
open Functor ⦃...⦄

module Gen {I : Set}
           (Σ : (I → I → Set₁) → (I → I → Set₁)) ⦃ fΣ : Functor Σ ⦄
           (L : Lawful Σ)
           (i₀ j₀ k₀ m₀ : I)
           (D : I → I → Set₁)
           (αD : ∀ {a j} → Σ D a j → D a j) where

  open Lawful L

  -- hop fra tilstand k med en X ender i D k j₀
  J : I → Set → Set₁
  J k X = X → D k j₀

  S : (I → I → Set₁) → (I → I → Set₁)
  S = Exc J + Σ

  -- bærertype: "kør med en handler hd, der kan køres fra enhver fejltilstand"
  C : I → I → Set₁
  C i j = ((s : I) → D s j) → D i j

  algE : ∀ {i} → S C i j₀ → C i j₀  
  algE {i} (i₁ throw)         = λ hd → hd i
  algE (i₁ (end l x))         = λ hd → l x
  algE (i₁ (catch p h k))     = λ hd → p (λ x → k x hd) (λ s → h s hd)
  algE (i₂ x)                 = λ hd → αD (fmap (λ {a} m → m hd) x)

  postulate lawfulExc : Lawful (Exc J)

  lawfulS : Lawful S
  lawfulS = lawful+ lawfulExc L

  ----------------------------------------------------------------------
  -- Catch-End: catch (λ ℓ → end ℓ x) h k ≡ k x

  eq-Catch-End : (X : Set) (A : Set₁) → Equation S (X × ((s : I) → Free S A s j₀) × (X → Free S A i₀ j₀)) A i₀ j₀
  eq-Catch-End X A =
    (λ { (x , h , k) → op (i₁ (catch {i = i₀} {k = i₀} (λ ℓ → op (i₁ (end ℓ x))) h k)) })
    ≐ (λ { (x , h , k) → k x })

  eq-Catch-End-ok : ∀ X A → respects {Σ = S} {C = C} {j = j₀} algE (eq-Catch-End X A)
  eq-Catch-End-ok X A ρ (x , h , k) = refl

  ----------------------------------------------------------------------
  -- Catch-Throw: catch (λ _ → throw) h k ≡ h i₀

  eq-Catch-Throw : (X : Set) (A : Set₁)
                 → Equation S (((s : I) → Free S A s j₀) × (X → Free S A k₀ j₀)) A i₀ j₀
  eq-Catch-Throw X A =
    (λ { (h , k) → op (i₁ (catch {k = k₀} (λ _ → op (i₁ throw)) h k)) })
    ≐ (λ { (h , k) → h i₀ })

  eq-Catch-Throw-ok : ∀ X A → respects {Σ = S} {C = C} {j = j₀} algE (eq-Catch-Throw X A)
  eq-Catch-Throw-ok X A ρ (h , k) = refl

  ----------------------------------------------------------------------
  -- End-Through: catch (λ _ → end ℓ x) h k ≡ end ℓ x

  eq-end-through : (X W : Set) (A : Set₁)
                 → Equation S (J i₀ W × W × ((s : I) → Free S A s j₀) × (X → Free S A k₀ j₀)) A i₀ j₀
  eq-end-through X W A =
    (λ { (ℓ , x , h , k) → op (i₁ (catch {k = k₀} (λ _ → op (i₁ (end ℓ x))) h k)) })
    ≐ (λ { (ℓ , x , h , k) → op (i₁ (end ℓ x)) })

  eq-end-through-ok : ∀ X W A → respects {Σ = S} {C = C} {j = j₀} algE (eq-end-through X W A)
  eq-end-through-ok X W A ρ (ℓ , x , h , k) = refl


  -- -- eq3 Catch-Bind:

  -- eq3 : (X : Set) (A : Set₁) → Equation S (WFTerm X × (X → Free S A k₀ j₀)) A i₀ j₀
  -- eq3 X A = (λ { (wft p _ , k) →
  --      op (i₁ (catch {k = k₀} {A = X}
  --                (λ ℓ → p >>= λ { (lift x) → op (i₁ (end ℓ x)) })
  --                (λ _ → op (i₁ throw))
  --                k)) }) ≐ (λ { (wft p _ , k) → p >>= k })

  ----------------------------------------------------------------------
  -- Bind-lovene

  -- End-Bind: end ℓ x >>= f ≡ end ℓ x
  eq-Bind-lovene : (W : Set) (B : Set₁) → Equation S (J i₀ W × W) B i₀ j₀
  eq-Bind-lovene W B =
    (λ { (ℓ , x) → op (i₁ (end {j = k₀} ℓ x)) >>= λ (_ : Lift (suc zero) ⊥) → op (i₁ throw) })
    ≐ (λ { (ℓ , x) → op (i₁ (end ℓ x)) })

  eq-Bind-lovene-ok : ∀ W B → respects {Σ = S} {C = C} {j = j₀} algE (eq-Bind-lovene W B)
  eq-Bind-lovene-ok W B ρ (ℓ , x) = refl

  -- Throw-Bind: throw >>= f ≡ throw
  eq-Throw-Bind : (B : Set₁) → Equation S ⊤ B i₀ j₀
  eq-Throw-Bind B =
    (λ _ → op (i₁ (throw {j = k₀})) >>= λ (_ : Lift (suc zero) ⊥) → op (i₁ throw))
    ≐ (λ _ → op (i₁ throw))

  eq-Throw-Bind-ok : ∀ B → respects {Σ = S} {C = C} {j = j₀} algE (eq-Throw-Bind B)
  eq-Throw-Bind-ok B ρ tt = refl

  -- Catch-Distr: catch p h k >>= f ≡ catch (λ ℓ → p ℓ >>= f) (λ s → h s >>= f) (λ a → k a >>= f)
  eq-Catch-Distr : (W : Set) (Y B : Set₁)
                 → Equation S ((J m₀ W → Free S Y i₀ k₀)
                             × ((s : I) → Free S Y s k₀)
                             × (W → Free S Y m₀ k₀)
                             × (Y → Free S B k₀ j₀)) B i₀ j₀
  eq-Catch-Distr W Y B =
    (λ { (p , h , k , f) → op (i₁ (catch {A = W} p h k)) >>= f })
    ≐ (λ { (p , h , k , f) →
           op (i₁ (catch {k = m₀} {A = W}
                     (λ ℓ → p ℓ >>= f)
                     (λ s → h s >>= f)
                     (λ a → k a >>= f))) })

  eq-Catch-Distr-ok : ∀ W Y B → respects {Σ = S} {C = C} {j = j₀} algE (eq-Catch-Distr W Y B)
  eq-Catch-Distr-ok W Y B ρ (p , h , k , f) = refl

  ----------------------------------------------------------------------
  -- Operationer og naturlighed

  OpT : Set → I → I → Set₂
  OpT B s n = ∀ {K : I → I → Set₁} {j} → (B → K n j) → Σ K s j

  NaturalAt : (B : Set) (s n : I) → OpT B s n → Set₂
  NaturalAt B s n o =
    ∀ {K L : I → I → Set₁} {j}
      (f : ∀ {a} → K a j → L a j) (c : B → K n j)
    → fmap {X = K} {Y = L} {j = j} {j' = j} f (o {K} {j} c)
      ≡ o {L} {j} (λ b → f {n} (c b))

  module Op {B : Set} {s n : I} (o : OpT B s n) (nat : NaturalAt B s n o) where

    fold-o : ∀ {A : Set₁}
               (ρ : A → C j₀ j₀)
               (c : B → Free S A n j₀) (hd : (x : I) → D x j₀)
           → fold {C = C} ρ algE (op (i₂ (o {Free S A} {j₀} c))) hd
             ≡ αD (o {D} {j₀} (λ b → fold {C = C} ρ algE (c b) hd))
    fold-o {A} ρ c hd =
      trans (cong αD (fmap-∘ {X = Free S A} {Y = C} {Z = D}
                             {j = j₀} {j' = j₀} {j'' = j₀}
                             (λ {a} m → m hd)
                             (fold {C = C} ρ algE)
                             (o {Free S A} {j₀} c)))
            (cong αD (nat {K = Free S A} {L = D} {j = j₀}
                          (λ {a} t → fold {C = C} ρ algE t hd) c))

  module Inter (B : Set) (n₀ : I)
               (o : OpT B i₀ n₀)
               (nat : NaturalAt B i₀ n₀ o)
               (X : Set) (A : Set₁) where

    -- Catch-Op: catch (λ ℓ → o (λ b → m ℓ b)) h k ≡ o (λ b → catch (λ ℓ → m ℓ b) h k)
    eq-Catch-Op : Equation S ((J m₀ X → B → Free S A n₀ j₀)
                            × ((s : I) → Free S A s j₀)
                            × (X → Free S A m₀ j₀)) A i₀ j₀
    eq-Catch-Op =
      (λ { (m , h , k) →
           op (i₁ (catch {k = m₀} {A = X}
                     (λ ℓ → op (i₂ (o (λ b → m ℓ b))))
                     h k)) })
      ≐ (λ { (m , h , k) →
             op (i₂ (o (λ b → op (i₁ (catch {i = n₀} {k = m₀} {A = X}
                                       (λ ℓ → m ℓ b) h k))))) })

    module O = Op {B} {i₀} {n₀} o nat

    eq-Catch-Op-ok : respects {Σ = S} {C = C} {j = j₀} algE eq-Catch-Op
    eq-Catch-Op-ok ρ (m , h , k) = funext (λ hd →
      trans
        (O.fold-o ρ (λ b → m (λ x → fold {C = C} ρ algE (k x) hd) b)
                    (λ s → fold {C = C} ρ algE (h s) hd))
        (sym (O.fold-o ρ
               (λ b → op (i₁ (catch {i = n₀} {k = m₀} {A = X}
                                 (λ ℓ → m ℓ b) h k)))
               hd)))

  ----------------------------------------------------------------------
  -- Comm: to operationer, der kommuterer

  castOp : ∀ {B s n n'} → n ≡ n' → OpT B s n → OpT B s n'
  castOp refl o = o

  castNat : ∀ {B s n n'} {o : OpT B s n} (e : n ≡ n')
          → NaturalAt B s n o → NaturalAt B s n' (castOp e o)
  castNat refl nat = nat

  module Comm (B₁ B₂ : Set) (p₁ p₂ q : I)
            (o₁  : OpT B₁ i₀ p₁) (n₁  : NaturalAt B₁ i₀ p₁ o₁)
            (o₂  : OpT B₂ p₁ q)  (n₂  : NaturalAt B₂ p₁ q  o₂)
            (o₂' : OpT B₂ i₀ p₂) (n₂' : NaturalAt B₂ i₀ p₂ o₂')
            (o₁' : OpT B₁ p₂ q)  (n₁' : NaturalAt B₁ p₂ q  o₁')
            (commD : ∀ (u : B₁ → B₂ → D q j₀)
                   → αD (o₁  {D} {j₀} (λ a₁ → αD (o₂  {D} {j₀} (λ a₂ → u a₁ a₂))))
                   ≡ αD (o₂' {D} {j₀} (λ a₂ → αD (o₁' {D} {j₀} (λ a₁ → u a₁ a₂))))) where

    module O₁  = Op o₁  n₁
    module O₂  = Op o₂  n₂
    module O₂' = Op o₂' n₂'
    module O₁' = Op o₁' n₁'

    eqComm : (A : Set₁) → Equation S (B₁ → B₂ → Free S A q j₀) A i₀ j₀
    eqComm A =
        (λ k → op (i₂ (o₁ (λ a₁ → op (i₂ (o₂ (λ a₂ → k a₁ a₂)))))))
        ≐ (λ k → op (i₂ (o₂' (λ a₂ → op (i₂ (o₁' (λ a₁ → k a₁ a₂)))))))

    eqComm-ok : ∀ A → respects {Σ = S} {C = C} {j = j₀} algE (eqComm A)
    eqComm-ok A ρ k = funext (λ hd →
        trans (O₁.fold-o ρ (λ a₁ → op (i₂ (o₂ (λ a₂ → k a₁ a₂)))) hd)
        (trans (cong (λ u → αD (o₁ {D} {j₀} u))
                    (funext (λ a₁ → O₂.fold-o ρ (λ a₂ → k a₁ a₂) hd)))
        (trans (commD (λ a₁ a₂ → fold {C = C} ρ algE (k a₁ a₂) hd))
        (trans (cong (λ u → αD (o₂' {D} {j₀} u))
                    (funext (λ a₂ → sym (O₁'.fold-o ρ (λ a₁ → k a₁ a₂) hd))))
            (sym (O₂'.fold-o ρ (λ a₂ → op (i₂ (o₁' (λ a₁ → k a₁ a₂)))) hd))))))

  ----------------------------------------------------------------------
  -- NoPure / WF (til udledning af Catch-Bind i EquivalentComputations)



  {-# NO_POSITIVITY_CHECK #-}
  data NoPure {R : Set₁} : ∀ {i j} → Free S R i j → Set₁ where
    np-throw : ∀ {i j} → NoPure {i = i} {j = j} (op (i₁ throw))
    np-end   : ∀ {k j} {W : Set} (ℓ : J k W) (y : W)
             → NoPure {i = k} {j = j} (op (i₁ (end ℓ y)))
    np-op    : ∀ {i j} (x : Σ (Free S R) i j) → All NoPure x → NoPure (op (i₂ x))
    np-catch : ∀ {i j k} {W : Set}
                 (p : J k W → Free S R i j) (h : (s : I) → Free S R s j)
                 (c : W → Free S R k j)
             → (∀ ℓ → NoPure (p ℓ)) → (∀ s → NoPure (h s)) → (∀ a → NoPure (c a))
             → NoPure (op (i₁ (catch p h c)))

  {-# NO_POSITIVITY_CHECK #-}
  data WF {R : Set₁} : ∀ {i j} → Free S R i j → Set₁ where
    wf-pure  : ∀ {i} (y : R) → WF {i = i} {j = i} (pure y)
    wf-throw : ∀ {i j} → WF {i = i} {j = j} (op (i₁ throw))
    wf-end   : ∀ {k j} {W : Set} (ℓ : J k W) (y : W)
             → WF {i = k} {j = j} (op (i₁ (end ℓ y)))
    wf-op    : ∀ {i j} (x : Σ (Free S R) i j) → All WF x → WF (op (i₂ x))
    wf-catch : ∀ {i j k} {W : Set}
                 (p : J k W → Free S R i j) (h : (s : I) → Free S R s j)
                 (c : W → Free S R k j)
             → (∀ ℓ → NoPure (p ℓ)) → (∀ s → WF (h s)) → (∀ a → WF (c a))
             → WF (op (i₁ (catch p h c)))



  ----------------------------------------------------------------------
  -- Udledning af Catch-Bind (eq3) i EquivalentComputations
  ----------------------------------------------------------------------



  record ExcBasicLaws (T : Theory S) : Set₂ where
    open EquivalentComputations T
    field
      has-Catch-End :
        ∀ {i} {X : Set} {A : Set₁}
          (x : X) (h : (s : I) → Free S A s j₀) (k : X → Free S A i j₀)
        → T ((λ (_ : Lift (suc zero) ⊤) → op (i₁ (catch {k = i} (λ ℓ → op (i₁ (end ℓ x))) h k)))
             ≐ (λ _ → k x))

      has-Catch-Throw :
        ∀ {i} {X : Set} {A : Set₁}
          (h : (s : I) → Free S A s j₀) (k : X → Free S A k₀ j₀)
        → T ((λ (_ : Lift (suc zero) ⊤) → op (i₁ (catch {k = k₀} (λ _ → op (i₁ throw)) h k)))
             ≐ (λ _ → h i))

      has-End-Through :
        ∀ {i} {X W : Set} {A : Set₁}
          (ℓ : J i W) (x : W) (h : (s : I) → Free S A s j₀) (k : X → Free S A k₀ j₀)
        → T ((λ (_ : Lift (suc zero) ⊤) → op (i₁ (catch {k = k₀} (λ _ → op (i₁ (end ℓ x))) h k)))
             ≐ (λ _ → op (i₁ (end ℓ x))))

      has-End-Bind :
        ∀ {i k} {W : Set} {R B : Set₁}
          (ℓ : J i W) (x : W) (f : R → Free S B k j₀)
        → T ((λ (_ : Lift (suc zero) ⊤) → op (i₁ (end {j = k} ℓ x)) >>= f)
              ≐ (λ _ → op (i₁ (end ℓ x))))

      has-Throw-Bind :
        ∀ {i k} {R B : Set₁}
          (f : R → Free S B k j₀)
        → T ((λ (_ : Lift (suc zero) ⊤) → op (i₁ (throw {i = i} {j = k})) >>= f)
              ≐ (λ _ → op (i₁ (throw {i = i}))))

      has-Catch-Distr :
        ∀ {i k m} {W : Set} {Y B : Set₁}
          (p : J m W → Free S Y i k) (h : (s : I) → Free S Y s k)
          (c : W → Free S Y m k) (f : Y → Free S B k j₀)
        → T ((λ (_ : Lift (suc zero) ⊤) → op (i₁ (catch {A = W} p h c)) >>= f)
             ≐ (λ _ → op (i₁ (catch {k = m} {A = W}
                                (λ ℓ → p ℓ >>= f)
                                (λ s → h s >>= f)
                                (λ a → c a >>= f)))))

      has-Catch-Σ :
        ∀ {i} {X : Set} {Y : Set₁}
          (x : Σ (Free S (Lift (suc zero) X)) i k₀)
          (h : (s : I) → Free S Y s j₀) (k : X → Free S Y k₀ j₀)
        → T ((λ (_ : Lift (suc zero) ⊤) →
               op (i₁ (catch {k = k₀} {A = X}
                         (λ ℓ → op (i₂ (fmap (λ m → m >>= λ { (lift a) → op (i₁ (end ℓ a)) }) x)))
                         h k)))
             ≐ (λ _ →
               op (i₂ (fmap (λ q → op (i₁ (catch {k = k₀} {A = X}
                                             (λ ℓ → q >>= λ { (lift a) → op (i₁ (end ℓ a)) })
                                             h k))) x))))

      has-Catch-Catch :
        ∀ {i m} {X W : Set} {Y : Set₁}
          (p : J m W → Free S (Lift (suc zero) X) i k₀)
          (h : (s : I) → Free S (Lift (suc zero) X) s k₀)
          (c : W → Free S (Lift (suc zero) X) m k₀)
          (k : X → Free S Y k₀ j₀)
        → T ((λ (_ : Lift (suc zero) ⊤) →
               op (i₁ (catch {k = k₀} {A = X}
                         (λ ℓ → op (i₁ (catch {k = m} {A = W}
                                           (λ ℓ' → p ℓ' >>= λ { (lift a) → op (i₁ (end ℓ a)) })
                                           (λ s → h s >>= λ { (lift a) → op (i₁ (end ℓ a)) })
                                           (λ a' → c a' >>= λ { (lift a) → op (i₁ (end ℓ a)) }))))
                         (λ _ → op (i₁ throw))
                         k)))
             ≐ (λ _ →
               op (i₁ (catch {k = m} {A = W}
                         (λ ℓ' → op (i₁ (catch {k = k₀} {A = X}
                                           (λ ℓ → p ℓ' >>= λ { (lift a) → op (i₁ (end ℓ a)) })
                                           (λ _ → op (i₁ throw))
                                           k)))
                         (λ s → op (i₁ (catch {k = k₀} {A = X}
                                         (λ ℓ → h s >>= λ { (lift a) → op (i₁ (end ℓ a)) })
                                         (λ _ → op (i₁ throw))
                                         k)))
                         (λ a' → op (i₁ (catch {k = k₀} {A = X}
                                           (λ ℓ → c a' >>= λ { (lift a) → op (i₁ (end ℓ a)) })
                                           (λ _ → op (i₁ throw))
                                           k)))))))

      has-Catch-NoJump :
        ∀ {i} {X : Set} {Y : Set₁}
          (q : Free S Y i j₀) (k : X → Free S Y k₀ j₀)
        → T ((λ (_ : Lift (suc zero) ⊤) →
               op (i₁ (catch {k = k₀} {A = X} (λ _ → q) (λ _ → op (i₁ throw)) k)))
             ≐ (λ _ → q))

      cong-all :
        ∀ {i k} {A B : Set₁}
          (Q : ∀ {a} → Free S A a k → Set₁)
          (f₁ f₂ : ∀ {a} → Free S A a k → Free S B a j₀)
          (x : Σ (Free S A) i k)
        → All Q x
        → (∀ {a} (t : Free S A a k) → Q t → f₁ t ~ f₂ t)
        → op (i₂ (fmap f₁ x)) ~ op (i₂ (fmap f₂ x))

      catch-cong :
        ∀ {i k m} {W : Set} {A : Set₁}
          {p p' : J m W → Free S A i k}
          {h h' : (s : I) → Free S A s k}
          {c c' : W → Free S A m k}
        → (∀ ℓ → p ℓ ~ p' ℓ)
        → (∀ s → h s ~ h' s)
        → (∀ a → c a ~ c' a)
        → op (i₁ (catch {A = W} p h c)) ~ op (i₁ (catch {A = W} p' h' c'))

  module Derived (T : Theory S) (laws : ExcBasicLaws T) where
    open EquivalentComputations T
    open ExcBasicLaws laws

    {-# TERMINATING #-}
    use-eq : ∀ {A : Set₁} {i j : I} (e : Equation S (Lift (suc zero) ⊤) A i j)
           → T e → lhs e (lift tt) ~ rhs e (lift tt)
    use-eq {A} e te = ~eq₀ {B = A} te (lift tt)

    -- 1. Syntaktisk np-bind
    {-# TERMINATING #-}
    np-bind~ : ∀ {R B : Set₁} {i k : I} (f₁ f₂ : R → Free S B k j₀) {q : Free S R i k}
             → NoPure q → (q >>= f₁) ~ (q >>= f₂)
    np-bind~ {R} {B} {i = i} {k = k} f₁ f₂ np-throw =
      ~trans (use-eq _ (has-Throw-Bind {i = i} {k = k} {R = R} {B = B} f₁))
             (~sym (use-eq _ (has-Throw-Bind {i = i} {k = k} {R = R} {B = B} f₂)))
    np-bind~ {R} {B} {k = k} f₁ f₂ (np-end ℓ y) =
      ~trans (use-eq _ (has-End-Bind {k = k} {R = R} {B = B} ℓ y f₁))
             (~sym (use-eq _ (has-End-Bind {k = k} {R = R} {B = B} ℓ y f₂)))
    np-bind~ f₁ f₂ (np-op x nx) =
      cong-all NoPure (_>>= f₁) (_>>= f₂) x nx (λ t nt → np-bind~ f₁ f₂ nt)
    np-bind~ f₁ f₂ (np-catch p h c np nh nc) =
      ~trans (use-eq _ (has-Catch-Distr p h c f₁))
             (~trans (catch-cong (λ ℓ → np-bind~ f₁ f₂ (np ℓ))
                                 (λ s → np-bind~ f₁ f₂ (nh s))
                                 (λ a → np-bind~ f₁ f₂ (nc a)))
                     (~sym (use-eq _ (has-Catch-Distr p h c f₂))))
    -- 2. Hovedteorem: Catch-Bind (eq3)
    {-# TERMINATING #-}
    eq3-derived : ∀ {X : Set} {Y : Set₁} {i : I}
                  (p : Free S (Lift (suc zero) X) i k₀)
                  (k : X → Free S Y k₀ j₀)
                → WF p
                → op (i₁ (catch {k = k₀} {A = X}
                           (λ ℓ → p >>= λ { (lift x) → op (i₁ (end ℓ x)) })
                           (λ _ → op (i₁ throw))
                           k))
                  ~ (p >>= λ { (lift x) → k x })
    eq3-derived {Y = Y} (pure (lift x)) k (wf-pure _) =
      use-eq _ (has-Catch-End x (λ _ → op  {A = Y} (i₁ throw)) k)
    eq3-derived {X} {i = i} _ k wf-throw =
      ~trans (catch-cong (λ ℓ → use-eq _ (has-Throw-Bind {i = i} {k = k₀} {R = Lift (suc zero) X}
                                                      (λ { (lift x) → op (i₁ (end ℓ x)) })))
                        (λ _ → ~refl)
                        (λ _ → ~refl))
            (~trans (use-eq _ (has-Catch-Throw {i = i} (λ _ → op (i₁ throw)) k))
                    (~sym (use-eq _ (has-Throw-Bind {i = i} {k = k₀} {R = Lift (suc zero) X}
                                                  (λ { (lift x) → k x })))))
    eq3-derived {X} _ k (wf-end ℓ y) =
      ~trans (catch-cong (λ ℓ' → use-eq _ (has-End-Bind {k = k₀} {R = Lift (suc zero) X}
                                                      ℓ y (λ { (lift x) → op (i₁ (end ℓ' x)) })))
                          (λ _ → ~refl)
                          (λ _ → ~refl))
              (~trans (use-eq _ (has-End-Through ℓ y (λ _ → op (i₁ throw)) k))
                      (~sym (use-eq _ (has-End-Bind {k = k₀} {R = Lift (suc zero) X}
                                                  ℓ y (λ { (lift x) → k x })))))
    eq3-derived (op (i₂ x)) k (wf-op .x wx) =
      ~trans (use-eq _ (has-Catch-Σ x (λ _ → op (i₁ throw)) k))
             (cong-all WF
              (λ q → op (i₁ (catch {k = k₀} (λ ℓ → q >>= λ { (lift a) → op (i₁ (end ℓ a)) })
                                  (λ _ → op (i₁ throw)) k)))
              (λ q → q >>= λ { (lift x) → k x })
              x wx
              (λ q wq → eq3-derived q k wq))
    eq3-derived (op (i₁ (catch b h c))) k (wf-catch .b .h .c nb wh wk) =
      ~trans (catch-cong (λ ℓ → use-eq _ (has-Catch-Distr b h c (λ { (lift a) → op (i₁ (end ℓ a)) })))
                          (λ _ → ~refl)
                          (λ _ → ~refl))
              (~trans (use-eq _ (has-Catch-Catch b h c k))
                      (~trans (catch-cong
                                (λ ℓ' → ~trans (catch-cong
                                                  (λ ℓ → np-bind~ (λ { (lift a) → op (i₁ (end ℓ a)) })
                                                                  (λ { (lift x) → k x })
                                                                  (nb ℓ'))
                                                  (λ _ → ~refl)
                                                  (λ _ → ~refl))
                                              (use-eq _ (has-Catch-NoJump (b ℓ' >>= λ { (lift x) → k x }) k)))
                                (λ s → eq3-derived (h s) k (wh s))
                                (λ a → eq3-derived (c a) k (wk a)))
                              (~sym (use-eq _ (has-Catch-Distr b h c (λ { (lift x) → k x }))))))