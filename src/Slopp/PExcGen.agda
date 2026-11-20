module Slopp.PExcGen where

open import Data.Unit using (⊤; tt)
open import Level using (suc; zero; Lift; lift)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Data.Product using (_×_; _,_)
open import Slopp.PHexc
open import Slopp.Lawful
-- open import Slopp.PEquivComp
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

----------------------------------------------------------------------
  -- Hjælpere

  cong₃ : ∀ {A B C′ E : Set₁} (f : A → B → C′ → E) {x y : A} {u v : B} {s t : C′}
        → x ≡ y → u ≡ v → s ≡ t → f x u s ≡ f y v t
  cong₃ f refl refl refl = refl

  ap : ((s : I) → D s j₀) → ∀ {a} → C a j₀ → D a j₀
  ap hd m = m hd

  ----------------------------------------------------------------------
  -- NoPure / WF. Handleren er nu (s : I) → …, og alle børn har samme slutindeks j.

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
  -- fold gennem en Σ-operation under bindT

  fold-op₂ : ∀ {V : I → I → Set₁} {R : Set₁} {i k : I}
               (ρ : ∀ {a} → V a j₀ → C a j₀) (f : R → Term S V k j₀)
               (x : Σ (Free S R) i k) (hd : (s : I) → D s j₀)
           → foldT {C = C} ρ algE (bindT {V = V} (op (i₂ x)) f) hd
           ≡ αD (fmap {X = Free S R} {Y = D} {j = k} {j' = j₀}
                   (λ {a} t → foldT {C = C} ρ algE (bindT {V = V} t f) hd) x)
  fold-op₂ {V} {R} {i} {k} ρ f x hd = cong αD
    (trans (fmap-∘ {X = Term S V} {Y = C} {Z = D} {j = j₀} {j' = j₀} {j'' = j₀}
                   (λ {a} m → m hd) (λ {a} t → foldT {C = C} ρ algE t)
                   (fmap {X = Free S R} {Y = Term S V} {j = k} {j' = j₀}
                         (λ {a} m → bindT {V = V} m f) x))
           (fmap-∘ {X = Free S R} {Y = Term S V} {Z = D} {j = k} {j' = j₀} {j'' = j₀}
                   (λ {a} t → foldT {C = C} ρ algE t hd)
                   (λ {a} m → bindT {V = V} m f) x))

  ----------------------------------------------------------------------
  -- NoPure-led: fortsættelsen kører aldrig i kroppen

  {-# TERMINATING #-}
  np-bind : ∀ {V : I → I → Set₁} {R : Set₁} {i k : I}
              (ρ : ∀ {a} → V a j₀ → C a j₀) (f₁ f₂ : R → Term S V k j₀)
              {q : Free S R i k}
          → NoPure q
          → foldT {C = C} ρ algE (bindT {V = V} q f₁)
          ≡ foldT {C = C} ρ algE (bindT {V = V} q f₂)
  np-bind ρ f₁ f₂ np-throw      = refl
  np-bind ρ f₁ f₂ (np-end ℓ y)  = refl
  np-bind ρ f₁ f₂ (np-op x nx)  =
    funext (λ hd →
      trans (fold-op₂ ρ f₁ x hd)
      (trans (cong αD (all-cong NoPure
                        (λ {a} t → foldT {C = C} ρ algE (bindT t f₁) hd)
                        (λ {a} t → foldT {C = C} ρ algE (bindT t f₂) hd)
                        x nx
                        (λ {a} t nt → cong (ap hd) (np-bind ρ f₁ f₂ nt))))
             (sym (fold-op₂ ρ f₂ x hd))))
  np-bind ρ f₁ f₂ (np-catch b h c nb nh nc) =
    funext (λ hd →
      cong₃ (λ Bv Hv Kv → Bv (λ x → Kv x hd) (λ s → Hv s hd))
            (funext (λ ℓ → np-bind ρ f₁ f₂ (nb ℓ)))
            (funext (λ s → np-bind ρ f₁ f₂ (nh s)))
            (funext (λ a → np-bind ρ f₁ f₂ (nc a))))

  ----------------------------------------------------------------------
  -- Catch-Bind: catch (λ ℓ → p >>= end ℓ) (λ s → throw) k' ≡ p >>= k'   (p veldannet)

  record WFTerm (X : Set) : Set₁ where
    constructor wft
    field
      term : Free S (Lift (suc zero) X) i₀ k₀
      wf   : WF term

  -- "p >>= end ℓ" og "p >>= k'" som fortsættelser
  K1 : (X : Set) → (X → D k₀ j₀) → Lift (suc zero) X → Term S (MV X) k₀ j₀
  K1 X J′ (lift x) = opT (i₁ (end {k = k₀} {A = X} J′ x))

  K2 : (X : Set) → Lift (suc zero) X → Term S (MV X) k₀ j₀
  K2 X (lift x) = var (kw x)

  eq3 : (X : Set) → Equation S (WFTerm X) (MV X) i₀ j₀
  eq3 X = (λ{ (wft p _) →
              opT (i₁ (catch {k = k₀} {A = X}
                             (λ ℓ → bindT p (K1 X ℓ))
                             (λ s → opT (i₁ throw))
                             (λ a → var (kw a)))) })
          ≐ (λ{ (wft p _) → bindT p (K2 X) })

  {-# TERMINATING #-}
  main : ∀ (X : Set) (ρ : ∀ {a} → MV X a j₀ → C a j₀)
           {i : I} {p : Free S (Lift (suc zero) X) i k₀}
       → WF p → ∀ (hd : (s : I) → D s j₀)
       → foldT {C = C} ρ algE (bindT p (K1 X (λ a → ρ (kw a) hd))) hd
       ≡ foldT {C = C} ρ algE (bindT p (K2 X)) hd
  main X ρ (wf-pure (lift y)) hd = refl
  main X ρ wf-throw           hd = refl
  main X ρ (wf-end ℓ y)       hd = refl
  main X ρ (wf-op x wx)       hd =
    trans (fold-op₂ ρ (K1 X (λ a → ρ (kw a) hd)) x hd)
    (trans (cong αD (all-cong WF
                      (λ {a} t → foldT {C = C} ρ algE (bindT t (K1 X (λ a′ → ρ (kw a′) hd))) hd)
                      (λ {a} t → foldT {C = C} ρ algE (bindT t (K2 X)) hd)
                      x wx
                      (λ {a} t wt → main X ρ wt hd)))
           (sym (fold-op₂ ρ (K2 X) x hd)))
  main X ρ (wf-catch b h c nb wh wk) hd =
    cong₃ (λ Bv Jv Hv → Bv Jv Hv)
          (funext (λ ℓ → np-bind ρ (K1 X (λ a → ρ (kw a) hd)) (K2 X) (nb ℓ)))
          (funext (λ a → main X ρ (wk a) hd))
          (funext (λ s → main X ρ (wh s) hd))

  eq3-ok : ∀ X → respects {Σ = S} {C = C} {j = j₀} algE (eq3 X)
  eq3-ok X ρ (wft p wf) = funext (λ hd → main X ρ wf hd)

  -- eq3 : (X : Set) → Equation S (Free S (Lift (suc zero) X) i₀ k₀) (MV X) i₀ j₀
  -- eq3 X = (λ p →
  --             opT (i₁ (catch {k = k₀} {A = X}
  --                            (λ ℓ → bindT p (λ { (lift x) → opT (i₁ (end ℓ x)) }))
  --                            (λ s → opT (i₁ throw))
  --                            (λ a → var (kw a)))))
  --         ≐ (λ p → bindT p (λ { (lift x) → var (kw x) }))

  -- -- Bemærk: loven gælder ikke for alle p (jf. WF-eksemplet), så beviset er et hul.
  -- eq3-ok : ∀ X → respects {Σ = S} {C = C} {j = j₀} algE (eq3 X)
  -- eq3-ok X ρ p = {!  !}

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





  -- Operationer og naturlighed med vilkårligt start- og slutindeks

  OpT : Set → I → I → Set₂
  OpT B s n = ∀ {K : I → I → Set₁} {j} → (B → K n j) → Σ K s j

  NaturalAt : (B : Set) (s n : I) → OpT B s n → Set₂
  NaturalAt B s n o =
    ∀ {K L : I → I → Set₁} {j}
      (f : ∀ {a} → K a j → L a j) (c : B → K n j)
    → fmap {X = K} {Y = L} {j = j} {j' = j} f (o {K} {j} c)
      ≡ o {L} {j} (λ b → f {n} (c b))

  -- fold-o: foldT ρ algE (o c) ≡ αD (o (λ b → foldT ρ algE (c b) hd))
  module Op {B : Set} {s n : I} (o : OpT B s n) (nat : NaturalAt B s n o) where

    fold-o : ∀ {V : I → I → Set₁}
               (ρ : ∀ {a} → V a j₀ → C a j₀)
               (c : B → Term S V n j₀) (hd : (x : I) → D x j₀)
           → foldT {C = C} ρ algE (opT (i₂ (o {Term S V} {j₀} c))) hd
             ≡ αD (o {D} {j₀} (λ b → foldT {C = C} ρ algE (c b) hd))
    fold-o {V} ρ c hd =
      trans (cong αD (fmap-∘ {X = Term S V} {Y = C} {Z = D}
                             {j = j₀} {j' = j₀} {j'' = j₀}
                             (λ {a} m → m hd)
                             (λ {a} t → foldT {C = C} ρ algE t)
                             (o {Term S V} {j₀} c)))
            (cong αD (nat {K = Term S V} {L = D} {j = j₀}
                          (λ {a} t → foldT {C = C} ρ algE t hd) c))

  module Inter (B : Set) (n₀ : I)
               (o : OpT B i₀ n₀)
               (nat : NaturalAt B i₀ n₀ o)
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
    module O = Op {B} {i₀} {n₀} o nat

    eq-Catch-Op-ok : respects {Σ = S} {C = C} {j = j₀} algE eq-Catch-Op
    eq-Catch-Op-ok ρ tt = funext (λ hd →
      trans
        (O.fold-o ρ (λ b → var (mm (λ x → ρ (kk x) hd) b))
                    (λ s → ρ {s} hh hd))
        (sym (O.fold-o ρ
               (λ b → opT (i₁ (catch {i = n₀} {k = m₀} {A = X}
                                 (λ ℓ → var (mm ℓ b))
                                 (λ s → var hh)
                                 (λ a → var (kk a)))))
               hd)))

 
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

    data KVar : I → I → Set₁ where
      kk : B₁ → B₂ → KVar q j₀

    eqComm : Equation S ⊤ KVar i₀ j₀
    eqComm =
      (λ _ → opT (i₂ (o₁ (λ a₁ → opT (i₂ (o₂ (λ a₂ → var (kk a₁ a₂))))))))
      ≐ (λ _ → opT (i₂ (o₂' (λ a₂ → opT (i₂ (o₁' (λ a₁ → var (kk a₁ a₂))))))))

    eqComm-ok : respects {Σ = S} {C = C} {j = j₀} algE eqComm
    eqComm-ok ρ tt = funext (λ hd →
      trans (O₁.fold-o ρ (λ a₁ → opT (i₂ (o₂ (λ a₂ → var (kk a₁ a₂))))) hd)
      (trans (cong (λ u → αD (o₁ {D} {j₀} u))
                   (funext (λ a₁ → O₂.fold-o ρ (λ a₂ → var (kk a₁ a₂)) hd)))
      (trans (commD (λ a₁ a₂ → ρ (kk a₁ a₂) hd))
      (trans (cong (λ u → αD (o₂' {D} {j₀} u))
                   (funext (λ a₂ → sym (O₁'.fold-o ρ (λ a₁ → var (kk a₁ a₂)) hd))))
             (sym (O₂'.fold-o ρ (λ a₂ → opT (i₂ (o₁' (λ a₁ → var (kk a₁ a₂))))) hd))))))