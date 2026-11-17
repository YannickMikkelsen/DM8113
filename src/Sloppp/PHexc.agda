module Slopp.PHexc where

open import Data.Maybe using (Maybe; just; nothing)
open import Level using (Level; _⊔_; suc; zero)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; trans; sym)

postulate
  funext : ∀ {a b} {A : Set a} {B : A → Set b} {f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g

------------------------------------------------------------------------
-- Free indekseret monade: Free Σ A i j = beregning fra tilstand i til j

{-# NO_POSITIVITY_CHECK #-}
data Free {l : Level} {I : Set}
          (Σ : (I → I → Set l) → (I → I → Set l))
          (A : Set l) : I → I → Set l where
  pure : ∀ {i}   → A → Free Σ A i i
  op   : ∀ {i j} → Σ (Free Σ A) i j → Free Σ A i j

record Functor {l : Level} {I : Set}
               (F : (I → I → Set l) → (I → I → Set l)) : Set (suc l) where
  field
    fmap : ∀ {X Y} {j j'} → (∀ {i} → X i j → Y i j') → ∀ {i} → F X i j → F Y i j'

open Functor ⦃...⦄

{-# TERMINATING #-}
_>>=_ : ∀ {l} {I : Set} {Σ : (I → I → Set l) → (I → I → Set l)} {A B : Set l}
        ⦃ _ : Functor Σ ⦄ {i j k}
      → Free Σ A i j → (A → Free Σ B j k) → Free Σ B i k
pure x >>= f = f x
op s   >>= f = op (fmap (λ m → m >>= f) s)

{-# TERMINATING #-}
fold : ∀ {I} {Σ : (I → I → Set₁) → (I → I → Set₁)} {C : I → I → Set₁} ⦃ _ : Functor Σ ⦄
         {A : Set₁} {j : I}
     → (A → C j j)
     → (∀ {a} → Σ C a j → C a j)
     → ∀ {i} → Free Σ A i j → C i j
fold gen alg (pure x) = gen x
fold gen alg (op t)   = alg (fmap (fold gen alg) t)

------------------------------------------------------------------------
-- Signaturer

data _+_ {I : Set} (F G : (I → I → Set₁) → (I → I → Set₁))
         (X : I → I → Set₁) : I → I → Set₁ where
  i₁ : ∀ {i j} → F X i j → (F + G) X i j
  i₂ : ∀ {i j} → G X i j → (F + G) X i j

instance
  Functor+ : ∀ {I} {F G : (I → I → Set₁) → (I → I → Set₁)}
           → ⦃ Functor F ⦄ → ⦃ Functor G ⦄ → Functor (F + G)
  Functor+ = record
    { fmap = λ where
        f (i₁ s) → i₁ (fmap f s)
        f (i₂ s) → i₂ (fmap f s) }

data Fire {I : Set} (K : I → I → Set₁) : I → I → Set₁ where
  fire : ∀ {i j} → K i j → Fire K i j

instance
  fFire : ∀ {I} → Functor (Fire {I})
  fFire = record { fmap = λ where f (fire x) → fire (f x) }

data Abort {I : Set} (K : I → I → Set₁) : I → I → Set₁ where
  abort : ∀ {i j} → Abort K i j

instance
  fAbort : ∀ {I} → Functor (Abort {I})
  fAbort = record { fmap = λ where f abort → abort }

-- Opr: operationen går fra i til m, fortsættelsen fra m til j
data Opr {I : Set} (P : I → I → Set) (Ar : ∀ {i m} → P i m → Set)
         (K : I → I → Set₁) : I → I → Set₁ where
  opr : ∀ {i m j} (p : P i m) → (Ar p → K m j) → Opr P Ar K i j

instance
  fOpr : ∀ {I} {P : I → I → Set} {Ar : ∀ {i m} → P i m → Set}
       → Functor (Opr P Ar)
  fOpr = record { fmap = λ where f (opr p c) → opr p (λ b → f (c b)) }

-- Exc: J k A = et hop fra tilstand k med en A
data Exc {I : Set}
         (J : I → Set → Set₁)
         (K : I → I → Set₁)
         : I → I → Set₁ where

  throw : ∀ {i j} → Exc J K i j

  end   : ∀ {k j} {A : Set} → J k A → A → Exc J K k j

  catch : ∀ {i j k} {A : Set}
        → (J k A → K i j)
        → ((s : I) → K s j)
        → (A → K k j)
        → Exc J K i j

fmapExc : ∀ {I} {J : I → Set → Set₁} {X Y : I → I → Set₁} {j j'}
        → (∀ {i} → X i j → Y i j')
        → ∀ {i} → Exc J X i j → Exc J Y i j'
fmapExc f throw         = throw
fmapExc f (end l x)     = end l x
fmapExc f (catch p h k) = catch (λ l → f (p l)) (λ s → f (h s)) (λ x → f (k x))

instance
  fExc : ∀ {I} {J : I → Set → Set₁} → Functor (Exc J)
  fExc = record { fmap = fmapExc }

------------------------------------------------------------------------
-- Algebra for Exc

-- hop til en fortsættelse, der starter i k, tager en A og slutter i j₀
JΣ : ∀ {I} → ((I → I → Set₁) → (I → I → Set₁)) → Set₁ → I → I → Set → Set₁
JΣ Σ R j₀ k A = A → Free Σ (Maybe R) k j₀

T : ∀ {I} → (Σ : (I → I → Set₁) → (I → I → Set₁)) → Set₁ → I → I → Set₁
T Σ A i j = Free Σ (Maybe A) i j

-- givet en handler, der kan køres fra enhver fejltilstand s og slutter i j,
-- får vi en beregning fra i til j
H : ∀ {I} → (Σ : (I → I → Set₁) → (I → I → Set₁)) → Set₁ → I → I → Set₁
H {I} Σ A i j = ((s : I) → T Σ A s j) → T Σ A i j

genH : ∀ {I} {Σ : (I → I → Set₁) → (I → I → Set₁)} {A : Set₁} {i : I}
     → A → H Σ A i i
genH x = λ hd → pure (just x)

algH : ∀ {I} {Σ : (I → I → Set₁) → (I → I → Set₁)} {A : Set₁} ⦃ _ : Functor Σ ⦄ {j₀ : I}
     → ∀ {i} → (Exc (JΣ Σ A j₀) + Σ) (H Σ A) i j₀ → H Σ A i j₀
algH {i = i} (i₁ throw) = λ hd → hd i
algH (i₁ (end l x))     = λ hd → l x
algH (i₁ (catch p h k)) = λ hd → p (λ x → k x hd) (λ s → h s hd)
algH (i₂ x)             = λ hd → op (fmap (λ m → m hd) x)

-- den yderste throw bliver til abort
hexc : ∀ {I} {Σ' : (I → I → Set₁) → (I → I → Set₁)} {A : Set₁} ⦃ _ : Functor Σ' ⦄
     → ∀ {i j} → Free (Exc (JΣ (Abort + Σ') A j) + (Abort + Σ')) A i j
     → T (Abort + Σ') A i j
hexc {Σ' = Σ'} {A = A} m =
  fold {C = H (Abort + Σ') A} genH algH m (λ s → op (i₁ abort))


------------------------------------------------------------------------
-- Algebraiske teorier med parametre (Atkey, sektion 3)
--
-- Her er S en diskret kategori: kun en mængde I af tilstande, så
-- morfismerne f i e(f,v) og op(f,σ,{t_x}) er identiteter og udelades.

-- En S-parametriseret signatur: operationer p : P i m med arity Ar p,
-- domæne m og kodomæne i  (papirets  σ : i ← m^X).
record Sig (I : Set) : Set₁ where
  field
    P  : I → I → Set
    Ar : ∀ {i m} → P i m → Set

module Theories {I : Set} (Σ : Sig I) where
  open Sig Σ

  ----------------------------------------------------------------------
  -- Termer T_Σ(i, j, V)

  -- var   =  e(id, v)       (kun ved i = j, V er en uindekseret mængde)
  -- opT   =  op(id, σ, {t_x}), børnene ligger i T(m, j)
  data Term (V : Set) : I → I → Set₁ where
    var : ∀ {j} → V → Term V j j
    opT : ∀ {i m j} (p : P i m) → (Ar p → Term V m j) → Term V i j

  ----------------------------------------------------------------------
  -- Σ-algebraer (for fast slutindeks bliver a(i) = T(i, j, V))

  record Algebra (ℓ : Level) : Set (suc ℓ) where
    field
      Carrier : I → Set ℓ
      opA     : ∀ {i m} (p : P i m) → (Ar p → Carrier m) → Carrier i

  open Algebra

  -- afledte operationer [t] : a(j)^V → a(i)
  foldT : ∀ {ℓ} {V : Set} (A : Algebra ℓ) {i j}
        → (V → Carrier A j) → Term V i j → Carrier A i
  foldT A ρ (var v)   = ρ v
  foldT A ρ (opT p k) = opA A p (λ x → foldT A ρ (k x))

  -- termerne selv er en algebra
  TermAlg : (V : Set) (j : I) → Algebra (suc zero)
  TermAlg V j = record { Carrier = λ i → Term V i j
                       ; opA     = λ p k → opT p k }

  -- substitution = fold ind i term-algebraen
  bindT : ∀ {V W : Set} {i k j} → Term V i k → (V → Term W k j) → Term W i j
  bindT {W = W} {j = j} t σ = foldT (TermAlg W j) σ t

  -- homomorfier
  record Hom {ℓ ℓ'} (A : Algebra ℓ) (B : Algebra ℓ') : Set (ℓ ⊔ ℓ') where
    field
      map  : ∀ i → Carrier A i → Carrier B i
      pres : ∀ {i m} (p : P i m) (k : Ar p → Carrier A m)
           → map i (opA A p k) ≡ opA B p (λ x → map m (k x))

  ----------------------------------------------------------------------
  -- Term er fri Σ-algebra over V (uden ligninger)

  foldHom : ∀ {ℓ} {V : Set} (A : Algebra ℓ) {j}
          → (V → Carrier A j) → Hom (TermAlg V j) A
  foldHom A {j} ρ = record
    { map  = λ i t → foldT {_} {_} A {i} {j} ρ t
    ; pres = λ p k → refl }

  fold-unique : ∀ {ℓ} {V : Set} (A : Algebra ℓ) {j} (ρ : V → Carrier A j)
              → (h : Hom (TermAlg V j) A)
              → (∀ v → Hom.map h j (var v) ≡ ρ v)
              → ∀ {i} (t : Term V i j) → Hom.map h i t ≡ foldT A ρ t
  fold-unique A ρ h hv (var v)   = hv v
  fold-unique A ρ h hv (opT p k) =
    trans (Hom.pres h p k)
          (cong (opA A p) (funext (λ x → fold-unique A ρ h hv (k x))))

  -- substitutionslemma: [bind t σ]ρ = [t](λ v → [σ v]ρ)
  subst-lemma : ∀ {ℓ} {V W : Set} (A : Algebra ℓ) {i k j}
                (ρ : W → Carrier A j) (σ : V → Term W k j) (t : Term V i k)
              → foldT A ρ (bindT t σ) ≡ foldT A (λ v → foldT A ρ (σ v)) t
  subst-lemma A ρ σ (var v)   = refl
  subst-lemma A ρ σ (opT p k) =
    cong (opA A p) (funext (λ x → subst-lemma A ρ σ (k x)))

  ----------------------------------------------------------------------
  -- Ligninger og teorier (Σ, E)

  -- t = t' ∈ T(src, dst, Var), med en parametermængde Par
  -- (til fx den skrevne værdi y i writes(y)).
  record Equation : Set₁ where
    field
      Par      : Set
      Var      : Set
      src dst  : I
      lhs rhs  : Par → Term Var src dst

  record Theory : Set₁ where
    field
      Ax  : Set
      eqn : Ax → Equation

  -- en algebra opfylder en ligning: f ; [t] = f ; [t'] for alle valuationer f
  Respects : ∀ {ℓ} → Algebra ℓ → Equation → Set ℓ
  Respects A e =
    ∀ (ρ : Equation.Var e → Carrier A (Equation.dst e)) (g : Equation.Par e) →
      foldT A ρ (Equation.lhs e g) ≡ foldT A ρ (Equation.rhs e g)

  -- (Σ, E)-algebra = Σ-algebra der opfylder alle ligninger i E
  record Model (T : Theory) (ℓ : Level) : Set (suc ℓ) where
    field
      alg : Algebra ℓ
      sat : ∀ a → Respects alg (Theory.eqn T a)

  ----------------------------------------------------------------------
  -- Kongruens genereret af E, og frihed af Term/≈

  module _ (T : Theory) where

    infix 4 _≈_

    -- mindste kongruens (på hvert T(i, j, W)) lukket under ligningerne:
    -- ≈-ax er papirets regel  [t]t_x ≡ [t']t'_x  med substitution σ
    data _≈_ {W : Set} : ∀ {i j} → Term W i j → Term W i j → Set₁ where
      ≈-refl  : ∀ {i j} {t : Term W i j} → t ≈ t
      ≈-sym   : ∀ {i j} {t u : Term W i j} → t ≈ u → u ≈ t
      ≈-trans : ∀ {i j} {t u v : Term W i j} → t ≈ u → u ≈ v → t ≈ v
      ≈-op    : ∀ {i m j} (p : P i m) {k k' : Ar p → Term W m j}
              → (∀ x → k x ≈ k' x) → opT p k ≈ opT p k'
      ≈-ax    : ∀ {j} (a : Theory.Ax T)
                  (g : Equation.Par (Theory.eqn T a))
                  (σ : Equation.Var (Theory.eqn T a)
                       → Term W (Equation.dst (Theory.eqn T a)) j)
              → bindT (Equation.lhs (Theory.eqn T a) g) σ
                ≈ bindT (Equation.rhs (Theory.eqn T a) g) σ

    -- Eksistens i frihedsegenskaben: foldT ind i en hvilken som helst
    -- (Σ,E)-algebra respekterer ≈, så den faktorerer gennem Term/≈.
    -- (Entydighed følger af fold-unique, da Term → Term/≈ er surjektiv.)
    sound : ∀ {ℓ} (M : Model T ℓ) {W : Set} {i j} {t u : Term W i j}
            (ρ : W → Carrier (Model.alg M) j)
          → t ≈ u → foldT (Model.alg M) ρ t ≡ foldT (Model.alg M) ρ u
    sound M ρ ≈-refl        = refl
    sound M ρ (≈-sym p)     = sym (sound M ρ p)
    sound M ρ (≈-trans p q) = trans (sound M ρ p) (sound M ρ q)
    sound M ρ (≈-op p h)    =
      cong (opA (Model.alg M) p) (funext (λ x → sound M ρ (h x)))
    sound M ρ (≈-ax a g σ)  =
      trans (subst-lemma A ρ σ (Equation.lhs e g))
        (trans (Model.sat M a (λ v → foldT A ρ (σ v)) g)
               (sym (subst-lemma A ρ σ (Equation.rhs e g))))
      where A = Model.alg M
            e = Theory.eqn T a