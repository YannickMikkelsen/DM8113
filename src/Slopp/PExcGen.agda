-- {-# OPTIONS --allow-unsolved-metas #-}
module Slopp.PExcGen where

open import Data.Unit using (⊤; tt)
open import Level using (suc; zero; Lift; lift)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Data.Product using (_×_; _,_)
open import Slopp.PHexc
open import Slopp.Lawful
open Functor ⦃...⦄

-- Tom type i Set₁: generatorerne i Free er ubrugte, fordi alle "variable"
-- (handler, fortsættelser, ...) ligger i miljøet Γ som Free-programmer.
data ⊥₁ : Set₁ where

-- Exc-ligningerne for algebraen algE, kun udtrykt med Free
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

  -- fold af et Free-program med generatortolkning gen
  F : ∀ {B : Set₁} → (B → C j₀ j₀) → ∀ {i} → Free S B i j₀ → C i j₀
  F gen p = fold {Σ = S} {C = C} {j = j₀} gen algE p

  -- bind for S
  infixl 1 _>>=S_
  _>>=S_ : ∀ {B R : Set₁} {i k j : I}
         → Free S R i k → (R → Free S B k j) → Free S B i j
  m >>=S f = _>>=_ {Σ = S} m f

  -- Lovlighed af S = Exc J + Σ: Σ er givet, Exc J skal bevises
  postulate lawfulExc : Lawful (Exc J)   -- TODO: bevis (som for Fire, Abort, Opr)

  lawfulS : Lawful S
  lawfulS = lawful+ lawfulExc L

  -- Miljøtyper: variablene fra før er nu programmer i Γ
  -- handler, der kan køres fra enhver fejltilstand s
  Hd : Set₁
  Hd = (s : I) → Free S ⊥₁ s j₀

  -- fortsættelse, der starter i m og tager en X
  Kont : Set → I → Set₁
  Kont X m = X → Free S ⊥₁ m j₀

  ----------------------------------------------------------------------
  -- Catch-End: catch (λ ℓ → end ℓ x) h k' ≡ k' x

  eq-Catch-End : (X : Set) → Equation S (X × Hd × Kont X i₀) ⊥₁ i₀ j₀
  eq-Catch-End X =
      (λ { (x , hd , kt) → op (i₁ (catch {k = i₀} {A = X}
                                    (λ ℓ → op (i₁ (end ℓ x)))
                                    hd
                                    kt)) })
    ≐ (λ { (x , hd , kt) → kt x })

  eq-Catch-End-ok : ∀ X → respects {Σ = S} {C = C} {j = j₀} algE (eq-Catch-End X)
  eq-Catch-End-ok X gen (x , hd , kt) = refl

  ----------------------------------------------------------------------
  -- Catch-Throw: catch (λ _ → throw) h k' ≡ h

  eq-Catch-Throw : (X : Set) → Equation S (Hd × Kont X k₀) ⊥₁ i₀ j₀
  eq-Catch-Throw X =
      (λ { (hd , kt) → op (i₁ (catch {k = k₀} {A = X}
                                (λ _ → op (i₁ throw))
                                hd
                                kt)) })
    ≐ (λ { (hd , kt) → hd i₀ })

  eq-Catch-Throw-ok : ∀ X → respects {Σ = S} {C = C} {j = j₀} algE (eq-Catch-Throw X)
  eq-Catch-Throw-ok X gen (hd , kt) = refl

  ----------------------------------------------------------------------
  -- End-Through: catch (λ _ → end ℓ x) h k' ≡ end ℓ x

  Γ₃ : Set → Set₁
  Γ₃ X = J i₀ X × X

  eq-end-through : (X : Set) → Equation S (Γ₃ X × Hd × Kont X k₀) ⊥₁ i₀ j₀
  eq-end-through X =
      (λ { ((ℓ , x) , hd , kt) → op (i₁ (catch {k = k₀} {A = X}
                                          (λ _ → op (i₁ (end ℓ x)))
                                          hd
                                          kt)) })
    ≐ (λ { ((ℓ , x) , hd , kt) → op (i₁ (end ℓ x)) })

  eq-end-through-ok : ∀ X → respects {Σ = S} {C = C} {j = j₀} algE (eq-end-through X)
  eq-end-through-ok X gen ((ℓ , x) , hd , kt) = refl

  ----------------------------------------------------------------------
  -- Hjælpere

  cong₃ : ∀ {A B C′ E : Set₁} (f : A → B → C′ → E) {x y : A} {u v : B} {s t : C′}
        → x ≡ y → u ≡ v → s ≡ t → f x u s ≡ f y v t
  cong₃ f refl refl refl = refl

  ap : ((s : I) → D s j₀) → ∀ {a} → C a j₀ → D a j₀
  ap hd m = m hd

  ----------------------------------------------------------------------
  -- NoPure / WF. Handleren er (s : I) → …, og alle børn har samme slutindeks j.

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
  -- Fortsættelser til Catch-Bind

  -- kT X kt: fortsættelsen "k'" anvendt på en Lift X
  kT : (X : Set) → Kont X k₀ → Lift (suc zero) X → Free S ⊥₁ k₀ j₀
  kT X kt (lift x) = kt x

  -- "p >>= end ℓ" som fortsættelse
  K1 : (X : Set) → (X → D k₀ j₀) → Lift (suc zero) X → Free S ⊥₁ k₀ j₀
  K1 X ℓ (lift x) = op (i₁ (end {k = k₀} {A = X} ℓ x))

  -- det hop, som algE giver catch-kroppen: a ↦ ⟦kt a⟧ hd
  ℓ₀ : (X : Set) → (⊥₁ → C j₀ j₀) → Kont X k₀ → ((s : I) → D s j₀) → X → D k₀ j₀
  ℓ₀ X gen kt hd a = F gen (kt a) hd

  ----------------------------------------------------------------------
  -- fold gennem en Σ-operation under bind

  fold-op₂ : ∀ {B R : Set₁} {i k : I}
               (gen : B → C j₀ j₀) (f : R → Free S B k j₀)
               (x : Σ (Free S R) i k) (hd : (s : I) → D s j₀)
           → F gen (op (i₂ x) >>=S f) hd
           ≡ αD (fmap {X = Free S R} {Y = D} {j = k} {j' = j₀}
                   (λ {a} t → F gen (t >>=S f) hd) x)
  fold-op₂ {B} {R} {i} {k} gen f x hd = cong αD
    (trans (fmap-∘ {X = Free S B} {Y = C} {Z = D} {j = j₀} {j' = j₀} {j'' = j₀}
                   (λ {a} m → m hd) (λ {a} t → F gen t)
                   (fmap {X = Free S R} {Y = Free S B} {j = k} {j' = j₀}
                         (λ {a} m → m >>=S f) x))
           (fmap-∘ {X = Free S R} {Y = Free S B} {Z = D} {j = k} {j' = j₀} {j'' = j₀}
                   (λ {a} t → F gen t hd)
                   (λ {a} m → m >>=S f) x))

  ----------------------------------------------------------------------
  -- NoPure-led: fortsættelsen kører aldrig i kroppen

  {-# TERMINATING #-}
  np-bind : ∀ {B R : Set₁} {i k : I}
              (gen : B → C j₀ j₀) (f₁ f₂ : R → Free S B k j₀)
              {q : Free S R i k}
          → NoPure q
          → F gen (q >>=S f₁) ≡ F gen (q >>=S f₂)
  np-bind gen f₁ f₂ np-throw      = refl
  np-bind gen f₁ f₂ (np-end ℓ y)  = refl
  np-bind gen f₁ f₂ (np-op x nx)  =
    funext (λ hd →
      trans (fold-op₂ gen f₁ x hd)
      (trans (cong αD (all-cong NoPure
                        (λ {a} t → F gen (t >>=S f₁) hd)
                        (λ {a} t → F gen (t >>=S f₂) hd)
                        x nx
                        (λ {a} t nt → cong (ap hd) (np-bind gen f₁ f₂ nt))))
             (sym (fold-op₂ gen f₂ x hd))))
  np-bind gen f₁ f₂ (np-catch b h c nb nh nc) =
    funext (λ hd →
      cong₃ (λ Bv Hv Kv → Bv (λ x → Kv x hd) (λ s → Hv s hd))
            (funext (λ ℓ → np-bind gen f₁ f₂ (nb ℓ)))
            (funext (λ s → np-bind gen f₁ f₂ (nh s)))
            (funext (λ a → np-bind gen f₁ f₂ (nc a))))

  ----------------------------------------------------------------------
  -- Catch-Bind: catch (λ ℓ → p >>= end ℓ) (λ s → throw) k' ≡ p >>= k'   (p veldannet)

  record WFTerm (X : Set) : Set₁ where
    constructor wft
    field
      term : Free S (Lift (suc zero) X) i₀ k₀
      wf   : WF term

  {-# TERMINATING #-}
  main : ∀ (X : Set) (gen : ⊥₁ → C j₀ j₀) (kt : Kont X k₀)
           {i : I} {p : Free S (Lift (suc zero) X) i k₀}
       → WF p → ∀ (hd : (s : I) → D s j₀)
       → F gen (p >>=S K1 X (ℓ₀ X gen kt hd)) hd
       ≡ F gen (p >>=S kT X kt) hd
  main X gen kt (wf-pure (lift y)) hd = refl
  main X gen kt wf-throw           hd = refl
  main X gen kt (wf-end ℓ y)       hd = refl
  main X gen kt (wf-op x wx)       hd =
    trans (fold-op₂ gen (K1 X (ℓ₀ X gen kt hd)) x hd)
    (trans (cong αD (all-cong WF
                      (λ {a} t → F gen (t >>=S K1 X (ℓ₀ X gen kt hd)) hd)
                      (λ {a} t → F gen (t >>=S kT X kt) hd)
                      x wx
                      (λ {a} t wt → main X gen kt wt hd)))
           (sym (fold-op₂ gen (kT X kt) x hd)))
  main X gen kt (wf-catch b h c nb wh wk) hd =
    cong₃ (λ Bv Jv Hv → Bv Jv Hv)
          (funext (λ ℓ → np-bind gen (K1 X (ℓ₀ X gen kt hd)) (kT X kt) (nb ℓ)))
          (funext (λ a → main X gen kt (wk a) hd))
          (funext (λ s → main X gen kt (wh s) hd))

  eq3 : (X : Set) → Equation S (WFTerm X × Kont X k₀) ⊥₁ i₀ j₀
  eq3 X =
      (λ { (wft p _ , kt) →
            op (i₁ (catch {k = k₀} {A = X}
                          (λ ℓ → p >>=S K1 X ℓ)
                          (λ s → op (i₁ throw))
                          kt)) })
    ≐ (λ { (wft p _ , kt) → p >>=S kT X kt })

  eq3-ok : ∀ X → respects {Σ = S} {C = C} {j = j₀} algE (eq3 X)
  eq3-ok X gen (wft p wf , kt) = funext (λ hd → main X gen kt wf hd)

  ----------------------------------------------------------------------
  -- Bind-lovene. p, h, k er Free-programmer i Γ; fortsættelsen er kt i Γ.

  -- End-Bind: end ℓ x >>= f ≡ end ℓ x
  Γ₄ : Set → Set₁
  Γ₄ W = J i₀ W × W

  eq-Bind-lovene : (X W : Set) → Equation S (Γ₄ W × Kont X k₀) ⊥₁ i₀ j₀
  eq-Bind-lovene X W =
      (λ { ((ℓ , x) , kt) → op (i₁ (end ℓ x)) >>=S kT X kt })
    ≐ (λ { ((ℓ , x) , kt) → op (i₁ (end ℓ x)) })

  eq-Bind-lovene-ok : ∀ X W → respects {Σ = S} {C = C} {j = j₀} algE (eq-Bind-lovene X W)
  eq-Bind-lovene-ok X W gen ((ℓ , x) , kt) = refl

  -- Throw-Bind: throw >>= f ≡ throw
  eq-Throw-Bind : (X : Set) → Equation S (Kont X k₀) ⊥₁ i₀ j₀
  eq-Throw-Bind X =
      (λ kt → op (i₁ throw) >>=S kT X kt)
    ≐ (λ _ → op (i₁ throw))

  eq-Throw-Bind-ok : ∀ X → respects {Σ = S} {C = C} {j = j₀} algE (eq-Throw-Bind X)
  eq-Throw-Bind-ok X gen kt = refl

  -- Catch-Distr: catch p h k >>= f ≡ catch (λ ℓ → p ℓ >>= f) (λ s → h s >>= f) (λ a → k a >>= f)
  Γ₆ : Set → Set → Set₁
  Γ₆ X W = (J m₀ W → Free S (Lift (suc zero) X) i₀ k₀)
         × ((s : I) → Free S (Lift (suc zero) X) s k₀)
         × (W → Free S (Lift (suc zero) X) m₀ k₀)

  eq-Catch-Distr : (X W : Set) → Equation S (Γ₆ X W × Kont X k₀) ⊥₁ i₀ j₀
  eq-Catch-Distr X W =
      (λ { ((p , h , k) , kt) → op (i₁ (catch {A = W} p h k)) >>=S kT X kt })
    ≐ (λ { ((p , h , k) , kt) →
            op (i₁ (catch {k = m₀} {A = W}
                          (λ ℓ → p ℓ >>=S kT X kt)
                          (λ s → h s >>=S kT X kt)
                          (λ a → k a >>=S kT X kt))) })

  eq-Catch-Distr-ok : ∀ X W → respects {Σ = S} {C = C} {j = j₀} algE (eq-Catch-Distr X W)
  eq-Catch-Distr-ok X W gen ((p , h , k) , kt) = refl

  ----------------------------------------------------------------------
  -- Operationer og naturlighed med vilkårligt start- og slutindeks

  OpT : Set → I → I → Set₂
  OpT B s n = ∀ {K : I → I → Set₁} {j} → (B → K n j) → Σ K s j

  NaturalAt : (B : Set) (s n : I) → OpT B s n → Set₂
  NaturalAt B s n o =
    ∀ {K L : I → I → Set₁} {j}
      (f : ∀ {a} → K a j → L a j) (c : B → K n j)
    → fmap {X = K} {Y = L} {j = j} {j' = j} f (o {K} {j} c)
      ≡ o {L} {j} (λ b → f {n} (c b))

  -- fold-o: F gen (op (i₂ (o c))) hd ≡ αD (o (λ b → F gen (c b) hd))
  module Op {B : Set} {s n : I} (o : OpT B s n) (nat : NaturalAt B s n o) where

    fold-o : ∀ {V : Set₁}
               (gen : V → C j₀ j₀)
               (c : B → Free S V n j₀) (hd : (x : I) → D x j₀)
           → F gen (op (i₂ (o {Free S V} {j₀} c))) hd
             ≡ αD (o {D} {j₀} (λ b → F gen (c b) hd))
    fold-o {V} gen c hd =
      trans (cong αD (fmap-∘ {X = Free S V} {Y = C} {Z = D}
                             {j = j₀} {j' = j₀} {j'' = j₀}
                             (λ {a} m → m hd)
                             (λ {a} t → F gen t)
                             (o {Free S V} {j₀} c)))
            (cong αD (nat {K = Free S V} {L = D} {j = j₀}
                          (λ {a} t → F gen t hd) c))

  module Inter (B : Set) (n₀ : I)
               (o : OpT B i₀ n₀)
               (nat : NaturalAt B i₀ n₀ o)
               (X : Set) where

    -- Miljø for Catch-Op: h (fra enhver s), k' (fra m₀), m ℓ b (fra n₀)
    Mm : Set₁
    Mm = J m₀ X → B → Free S ⊥₁ n₀ j₀

    -- Catch-Op: catch (λ ℓ → o (λ b → m ℓ b)) h k' ≡ o (λ b → catch (λ ℓ → m ℓ b) h k')
    eq-Catch-Op : Equation S (Hd × Kont X m₀ × Mm) ⊥₁ i₀ j₀
    eq-Catch-Op =
        (λ { (hd , kt , mm) →
              op (i₁ (catch {k = m₀} {A = X}
                            (λ ℓ → op (i₂ (o (λ b → mm ℓ b))))
                            hd
                            kt)) })
      ≐ (λ { (hd , kt , mm) →
              op (i₂ (o (λ b → op (i₁ (catch {i = n₀} {k = m₀} {A = X}
                                             (λ ℓ → mm ℓ b)
                                             hd
                                             kt))))) })

    -- kræver nat (to gange, under funext over hd)
    module O = Op {B} {i₀} {n₀} o nat

    eq-Catch-Op-ok : respects {Σ = S} {C = C} {j = j₀} algE eq-Catch-Op
    eq-Catch-Op-ok gen (hd0 , kt , mm) = funext (λ hd →
      trans
        (O.fold-o gen (λ b → mm (λ x → F gen (kt x) hd) b)
                      (λ s → F gen (hd0 s) hd))
        (sym (O.fold-o gen
               (λ b → op (i₁ (catch {i = n₀} {k = m₀} {A = X}
                                 (λ ℓ → mm ℓ b)
                                 hd0
                                 kt)))
               hd)))

    -- Throw-Op: throw >>= (λ _ → o f) ≡ throw
    eq-Throw-Op : Equation S (B → Free S ⊥₁ n₀ j₀) ⊥₁ i₀ j₀
    eq-Throw-Op =
        (λ ff → op (i₁ throw)
                  >>=S (λ (_ : Lift (suc zero) X) → op (i₂ (o (λ b → ff b)))))
      ≐ (λ _ → op (i₁ throw))

    eq-Throw-Op-ok : respects {Σ = S} {C = C} {j = j₀} algE eq-Throw-Op
    eq-Throw-Op-ok gen ff = refl

    -- End-Op: end ℓ x >>= (λ _ → o f) ≡ end ℓ x
    Γ₉ : Set → Set₁
    Γ₉ W = J i₀ W × W

    eq-End-Op : (W : Set) → Equation S (Γ₉ W × (B → Free S ⊥₁ n₀ j₀)) ⊥₁ i₀ j₀
    eq-End-Op W =
        (λ { ((ℓ , x) , ff) →
              op (i₁ (end ℓ x))
                >>=S (λ (_ : Lift (suc zero) X) → op (i₂ (o (λ b → ff b)))) })
      ≐ (λ { ((ℓ , x) , ff) → op (i₁ (end ℓ x)) })

    eq-End-Op-ok : ∀ W → respects {Σ = S} {C = C} {j = j₀} algE (eq-End-Op W)
    eq-End-Op-ok W gen ((ℓ , x) , ff) = refl

  ----------------------------------------------------------------------
  -- Comm: to operationer, der kommuterer
  --   o₁ (λ a₁ → o₂ (λ a₂ → k a₁ a₂)) ≡ o₂' (λ a₂ → o₁' (λ a₁ → k a₁ a₂))
  -- i₀ --o₁--> p₁ --o₂--> q   og   i₀ --o₂'--> p₂ --o₁'--> q
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

    -- fortsættelsen kt a₁ a₂ starter i q og ender i j₀
    eqComm : Equation S (B₁ → B₂ → Free S ⊥₁ q j₀) ⊥₁ i₀ j₀
    eqComm =
      (λ kt → op (i₂ (o₁ (λ a₁ → op (i₂ (o₂ (λ a₂ → kt a₁ a₂)))))))
      ≐ (λ kt → op (i₂ (o₂' (λ a₂ → op (i₂ (o₁' (λ a₁ → kt a₁ a₂)))))))

    eqComm-ok : respects {Σ = S} {C = C} {j = j₀} algE eqComm
    eqComm-ok gen kt = funext (λ hd →
      trans (O₁.fold-o gen (λ a₁ → op (i₂ (o₂ (λ a₂ → kt a₁ a₂)))) hd)
      (trans (cong (λ u → αD (o₁ {D} {j₀} u))
                   (funext (λ a₁ → O₂.fold-o gen (λ a₂ → kt a₁ a₂) hd)))
      (trans (commD (λ a₁ a₂ → F gen (kt a₁ a₂) hd))
      (trans (cong (λ u → αD (o₂' {D} {j₀} u))
                   (funext (λ a₂ → sym (O₁'.fold-o gen (λ a₁ → kt a₁ a₂) hd))))
             (sym (O₂'.fold-o gen (λ a₂ → op (i₂ (o₁' (λ a₁ → kt a₁ a₂)))) hd))))))