module Slopp.CombinedFile where

-- Parameterized udgave: state + fil kombineres, og Gen (Exc-delen) lægges
-- ovenpå.

open import Data.Unit          using (⊤; tt)
open import Data.Maybe         using (Maybe; just; nothing)
open import Data.String        using (String)
open import Data.Product       using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)

open import Slopp.PHexc2
open import Slopp.Lawful
open import Slopp.StateSig
open import Slopp.FHAlg
open import Slopp.PExcGen2
open import Slopp.PEquivComp
open Functor ⦃...⦄

record ProjInjIndep {I A B : Set} (proj-a : I → A) (inj-b : I → B → I) : Set where
  field proj-inj : ∀ i v → proj-a (inj-b i v) ≡ proj-a i

record InjInjComm {I A B : Set} (inj-a : I → A → I) (inj-b : I → B → I) : Set where
  field inj-comm : ∀ i w v → inj-a (inj-b i v) w ≡ inj-b (inj-a i w) v


-- I er indeksmængden. i₀ j₀ k₀ m₀ er de faste indeks, som lovene i Gen
-- bruges med (j₀ er programmets slutindeks).
module FileAlg (I : Set) (A : Set₁) (i₀ j₀ k₀ m₀ : I) where

  -- Signatur: state + fil, begge rene indekserede funktorer
  Sg : (I → I → Set₁) → (I → I → Set₁)
  Sg = StateOp {I} + FileOpS {I}

  fSg : Functor Sg
  fSg = Functor+ ⦃ fState ⦄ ⦃ fFile ⦄

  lawfulSg : Lawful Sg ⦃ fSg ⦄
  lawfulSg = lawful+ ⦃ fState ⦄ ⦃ fFile ⦄ lawfulState lawfulFile

  R : Set₁
  R = Maybe A × I

  D : I → I → Set₁
  D i j = I → HF {I} R i j

  αD : ∀ {a j} → Sg D a j → D a j
  αD (i₁ (look proj k))   = λ s → k (proj s) s
  αD (i₁ (set inj val k)) = λ s → k (inj s val)
  αD {j = j} (i₂ f)       = λ s → algFile (fmap ⦃ fFile ⦄ {X = D} {Y = HF {I} R} {j = j} {j' = j}
                                               (λ {i} k → k s) f)

  module G = Gen Sg ⦃ fSg ⦄ lawfulSg i₀ j₀ k₀ m₀ D αD

  Full : (I → I → Set₁) → (I → I → Set₁)
  Full = G.S              -- = Exc J + (StateOp + FileOpS)

  fFull : Functor Full
  fFull = Functor+ ⦃ fExc ⦄ ⦃ fSg ⦄

  C : I → I → Set₁
  C = G.C

  algD : ∀ {a j} → Full C a j → C a j
  algD {i} (i₁ throw)       = λ hd → hd i
  algD (i₁ (end l x))       = λ hd → l x
  algD (i₁ (catch p h k))   = λ hd → p (λ x → k x hd) (λ s → h s hd)
  algD {j = j} (i₂ x)       = λ hd → αD (fmap ⦃ fSg ⦄ {X = C} {Y = D} {j = j} {j' = j} (λ m → m hd) x)


  ----------------------------------------------------------------------
  -- State-love.

  module StateLaws {a : Set} (proj : ProjL I a) (inj : InjL I a I) where

    data SV : Set₁ where
      tv  : SV
      kv  : a → SV
      kv2 : a → a → SV

    -- Look-Discard: look proj (λ _ → tv) ≡ tv
    eqLookDiscard : (i : I) → Equation Full ⊤ SV i i
    eqLookDiscard i =
      (λ _ → op (i₂ (i₁ (look proj (λ _ → pure tv)))))
      ≐ (λ _ → pure tv)

    -- Set-Look: set inj s (look proj (λ s' → kv s')) ≡ set inj s (kv s)
    --   side condition: proj (inj i s) ≡ s
    eqSetLook : (i : I) (s : a) → Equation Full ⊤ SV i (inj i s)
    eqSetLook i s =
      (λ _ → op (i₂ (i₁ (set inj s (op (i₂ (i₁ (look proj (λ s' → pure (kv s'))))))))))
      ≐ (λ _ → op (i₂ (i₁ (set inj s (pure (kv s))))))

    -- Look-Set: look proj (λ s → set inj s (end (λ _ → f) tt)) ≡ end (λ _ → f) tt
    --   side condition: inj st (proj st) ≡ st
    eqLookSet : (i : I) → Equation Full (I → HF {I} R i j₀) SV i j₀
    eqLookSet i =
      (λ f → op (i₂ (i₁ (look proj (λ s → op (i₂ (i₁ (set inj s (op (i₁ (end (λ _ → f) tt)))))))))))
      ≐ (λ f → op (i₁ (end (λ _ → f) tt)))

    -- Look-Look: look proj (λ s → look proj (λ s' → kv2 s s')) ≡ look proj (λ s → kv2 s s)
    eqLookLook : (i : I) → Equation Full ⊤ SV i i
    eqLookLook i =
      (λ _ → op (i₂ (i₁ (look proj (λ s →
                op (i₂ (i₁ (look proj (λ s' → pure (kv2 s s'))))))))))
      ≐ (λ _ → op (i₂ (i₁ (look proj (λ s → pure (kv2 s s))))))

    -- Set-Set: set inj s₁ (set inj s₂ tv) ≡ set inj s₂ tv
    --   side condition: inj (inj i s₁) s₂ ≡ inj i s₂
    eqSetSet : (i : I) (s₁ s₂ : a) → (inj (inj i s₁) s₂ ≡ inj i s₂)
             → Equation Full ⊤ SV i (inj (inj i s₁) s₂)
    eqSetSet i s₁ s₂ coh =
      (λ _ → op (i₂ (i₁ (set inj s₁ (op (i₂ (i₁ (set inj s₂ (pure tv)))))))))
      ≐ (λ _ → subst (Free Full SV i) (sym coh) (op (i₂ (i₁ (set inj s₂ (pure tv))))))

    ----------------------------------------------------------------------
    -- Beviser

    eqLookDiscard-ok : ∀ i
      → respects {Σ = Full} {C = C} ⦃ fFull ⦄ algD (eqLookDiscard i)
    eqLookDiscard-ok i ρ _ = refl

    eqSetLook-ok : ∀ i s
      → (∀ st s' → proj (inj st s') ≡ s')
      → respects {Σ = Full} {C = C} ⦃ fFull ⦄ algD (eqSetLook i s)
    eqSetLook-ok i s coh ρ _ =
      funext (λ hb → funext (λ st → cong (λ x → ρ (kv x) hb (inj st s)) (coh st s)))

    eqLookSet-ok : ∀ i
      → (coh : ∀ st → inj st (proj st) ≡ st)
      → respects {Σ = Full} {C = C} ⦃ fFull ⦄ algD (eqLookSet i)
    eqLookSet-ok i coh ρ f =
      funext (λ hd → funext (λ st → cong f (coh st)))

    eqLookLook-ok : ∀ i
      → respects {Σ = Full} {C = C} ⦃ fFull ⦄ algD (eqLookLook i)
    eqLookLook-ok i ρ _ = refl

    eqSetSet-ok : ∀ i s₁ s₂
      → (coh : ∀ st a₁ a₂ → inj (inj st a₁) a₂ ≡ inj st a₂)
      → respects {Σ = Full} {C = C} ⦃ fFull ⦄ algD (eqSetSet i s₁ s₂ (coh i s₁ s₂))
    eqSetSet-ok i s₁ s₂ coh ρ _ with inj (inj i s₁) s₂ | coh i s₁ s₂
    ... | .(inj i s₂) | refl =
      funext (λ hd → funext (λ st → cong (ρ tv hd) (coh st s₁ s₂)))


  ----------------------------------------------------------------------
  -- Fil-love

  module FileLaws where

    data FV : Set₁ where
      tt′ : FV
      kr  : String → FV
      kr2 : String → String → FV

    -- Open-Close: fopen getOCₒ pₒ injₒ f (fclose getOC꜀ p꜀ inj꜀ tt) ≡ tt
    --   side condition: inj꜀ (injₒ i SOpen) SClosed ≡ i
    eqOpenClose : (i : I)
                  (getOCₒ getOC꜀ : ProjF I)
                  (pₒ : getOCₒ i ≡ Closed)
                  (injₒ : InjF I Open I)
                  (p꜀ : getOC꜀ (injₒ i SOpen) ≡ Open)
                  (inj꜀ : InjF I Closed I)
                  (coh : inj꜀ (injₒ i SOpen) SClosed ≡ i)
                → Equation Full String FV i (inj꜀ (injₒ i SOpen) SClosed)
    eqOpenClose i getOCₒ getOC꜀ pₒ injₒ p꜀ inj꜀ coh =
      (λ f → op (i₂ (i₂ (fopen getOCₒ pₒ injₒ f
                (op (i₂ (i₂ (fclose getOC꜀ p꜀ inj꜀ (pure tt′)))))))))
      ≐ (λ _ → subst (Free Full FV i) (sym coh) (pure tt′))

    -- Write-Write: fwrite s₁ (fwrite s₂ tt) ≡ fwrite s₂ tt
    eqWriteWrite : (i : I) (getOC : ProjF I) (p : getOC i ≡ Open)
                 → Equation Full (String × String) FV i i
    eqWriteWrite i getOC p =
      (λ { (s₁ , s₂) → op (i₂ (i₂ (fwrite getOC p s₁
                (op (i₂ (i₂ (fwrite getOC p s₂ (pure tt′)))))))) })
      ≐ (λ { (_ , s₂) → op (i₂ (i₂ (fwrite getOC p s₂ (pure tt′)))) })

    -- Write-Read: fwrite s (fread (λ r → kr r)) ≡ fwrite s (kr s)
    eqWriteRead : (i : I) (getOC : ProjF I) (p : getOC i ≡ Open)
                → Equation Full String FV i i
    eqWriteRead i getOC p =
      (λ s → op (i₂ (i₂ (fwrite getOC p s
                (op (i₂ (i₂ (fread getOC p (λ r → pure (kr r))))))))))
      ≐ (λ s → op (i₂ (i₂ (fwrite getOC p s (pure (kr s))))))

    -- Read-Discard: fread (λ _ → tt) ≡ tt
    eqReadDiscard : (i : I) (getOC : ProjF I) (p : getOC i ≡ Open)
                  → Equation Full ⊤ FV i i
    eqReadDiscard i getOC p =
      (λ _ → op (i₂ (i₂ (fread getOC p (λ _ → pure tt′)))))
      ≐ (λ _ → pure tt′)

    -- Read-Write: fread (λ s → fwrite s tt) ≡ tt
    eqReadWrite : (i : I) (getOC : ProjF I) (p : getOC i ≡ Open)
                → Equation Full ⊤ FV i i
    eqReadWrite i getOC p =
      (λ _ → op (i₂ (i₂ (fread getOC p (λ s →
                op (i₂ (i₂ (fwrite getOC p s (pure tt′)))))))))
      ≐ (λ _ → pure tt′)

    -- Read-Read: fread (λ s → fread (λ s' → kr2 s s')) ≡ fread (λ s → kr2 s s)
    eqReadRead : (i : I) (getOC : ProjF I) (p : getOC i ≡ Open)
               → Equation Full ⊤ FV i i
    eqReadRead i getOC p =
      (λ _ → op (i₂ (i₂ (fread getOC p (λ s →
                op (i₂ (i₂ (fread getOC p (λ s' → pure (kr2 s s'))))))))))
      ≐ (λ _ → op (i₂ (i₂ (fread getOC p (λ s → pure (kr2 s s))))))

    ----------------------------------------------------------------------
    -- Beviser

    eqOpenClose-ok : ∀ i getOCₒ getOC꜀ pₒ injₒ p꜀ inj꜀
      → (coh : inj꜀ (injₒ i SOpen) SClosed ≡ i)
      → respects {Σ = Full} {C = C} ⦃ fFull ⦄ algD
                 (eqOpenClose i getOCₒ getOC꜀ pₒ injₒ p꜀ inj꜀ coh)
    eqOpenClose-ok i getOCₒ getOC꜀ pₒ injₒ p꜀ inj꜀ coh ρ f
      with inj꜀ (injₒ i SOpen) SClosed | coh
    ... | .i | refl = refl

    eqWriteWrite-ok : ∀ i getOC p
      → respects {Σ = Full} {C = C} ⦃ fFull ⦄ algD (eqWriteWrite i getOC p)
    eqWriteWrite-ok i getOC p ρ t = refl

    eqWriteRead-ok : ∀ i getOC p
      → respects {Σ = Full} {C = C} ⦃ fFull ⦄ algD (eqWriteRead i getOC p)
    eqWriteRead-ok i getOC p ρ t = refl

    eqReadDiscard-ok : ∀ i getOC p
      → respects {Σ = Full} {C = C} ⦃ fFull ⦄ algD (eqReadDiscard i getOC p)
    eqReadDiscard-ok i getOC p ρ t = refl

    eqReadWrite-ok : ∀ i getOC p
      → respects {Σ = Full} {C = C} ⦃ fFull ⦄ algD (eqReadWrite i getOC p)
    eqReadWrite-ok i getOC p ρ t = refl

    eqReadRead-ok : ∀ i getOC p
      → respects {Σ = Full} {C = C} ⦃ fFull ⦄ algD (eqReadRead i getOC p)
    eqReadRead-ok i getOC p ρ t = refl


  ----------------------------------------------------------------------
  -- Tensor-love (State × File)

  module TensorLaws {a : Set} (proj : ProjL I a) (inj : InjL I a I)
                    (getOC : ProjF I) (injₒ : InjF I Open I) (injc : InjF I Closed I)
                    (pi : ProjInjIndep getOC inj) (ic : InjInjComm injₒ inj) (ic′ : InjInjComm injc inj) where

    open ProjInjIndep pi
    open InjInjComm ic

    data TV : Set₁ where
      ka : a → TV
      kb : a → String → TV
      kr : String → TV
      ku : TV

    ----------------------------------------------------------------------
    -- Get × File

    -- Get-Fopen
    eqGetFopen : (i : I) (p : getOC i ≡ Closed) (f : String)
               → Equation Full ⊤ TV i (injₒ i SOpen)
    eqGetFopen i p f =
      (λ _ → op (i₂ (i₁ (look proj (λ s →
               op (i₂ (i₂ (fopen getOC p injₒ f (pure (ka s))))))))))
      ≐ (λ _ → op (i₂ (i₂ (fopen getOC p injₒ f
               (op (i₂ (i₁ (look proj (λ s → pure (ka s))))))))))

    -- Get-Fread
    eqGetFread : (i : I) (p : getOC i ≡ Open)
               → Equation Full ⊤ TV i i
    eqGetFread i p =
      (λ _ → op (i₂ (i₁ (look proj (λ s →
               op (i₂ (i₂ (fread getOC p (λ r → pure (kb s r))))))))))
      ≐ (λ _ → op (i₂ (i₂ (fread getOC p (λ r →
               op (i₂ (i₁ (look proj (λ s → pure (kb s r))))))))))

    -- Get-Fwrite
    eqGetFwrite : (i : I) (p : getOC i ≡ Open) (t : String)
                → Equation Full ⊤ TV i i
    eqGetFwrite i p t =
      (λ _ → op (i₂ (i₁ (look proj (λ s →
               op (i₂ (i₂ (fwrite getOC p t (pure (ka s))))))))))
      ≐ (λ _ → op (i₂ (i₂ (fwrite getOC p t
               (op (i₂ (i₁ (look proj (λ s → pure (ka s))))))))))

    -- Get-Fclose
    eqGetFclose : (i : I) (p : getOC i ≡ Open)
                → Equation Full ⊤ TV i (injc i SClosed)
    eqGetFclose i p =
      (λ _ → op (i₂ (i₁ (look proj (λ s →
               op (i₂ (i₂ (fclose getOC p injc (pure (ka s))))))))))
      ≐ (λ _ → op (i₂ (i₂ (fclose getOC p injc
               (op (i₂ (i₁ (look proj (λ s → pure (ka s))))))))))

    ----------------------------------------------------------------------
    -- Put × File

    -- Put-Fopen
    eqPutFopen : (i : I) (v : a) (p : getOC i ≡ Closed) (f : String)
               → Equation Full ⊤ TV i (injₒ (inj i v) SOpen)
    eqPutFopen i v p f =
      (λ _ → op (i₂ (i₁ (set inj v
               (op (i₂ (i₂ (fopen getOC (trans (proj-inj i v) p) injₒ f (pure ku)))))))))
      ≐ (λ _ → subst (Free Full TV i) (sym (inj-comm i SOpen v))
                 (op (i₂ (i₂ (fopen getOC p injₒ f
                   (op (i₂ (i₁ (set inj v (pure ku))))))))))

    -- Put-Fread
    eqPutFread : (i : I) (v : a) (p : getOC i ≡ Open)
               → Equation Full ⊤ TV i (inj i v)
    eqPutFread i v p =
      (λ _ → op (i₂ (i₁ (set inj v
               (op (i₂ (i₂ (fread getOC (trans (proj-inj i v) p) (λ r → pure (kr r))))))))))
      ≐ (λ _ → op (i₂ (i₂ (fread getOC p (λ r →
               op (i₂ (i₁ (set inj v (pure (kr r))))))))))

    -- Put-Fwrite
    eqPutFwrite : (i : I) (v : a) (p : getOC i ≡ Open) (t : String)
                → Equation Full ⊤ TV i (inj i v)
    eqPutFwrite i v p t =
      (λ _ → op (i₂ (i₁ (set inj v
               (op (i₂ (i₂ (fwrite getOC (trans (proj-inj i v) p) t (pure ku)))))))))
      ≐ (λ _ → op (i₂ (i₂ (fwrite getOC p t
               (op (i₂ (i₁ (set inj v (pure ku)))))))))

    -- Put-Fclose
    eqPutFclose : (i : I) (v : a) (p : getOC i ≡ Open)
                → Equation Full ⊤ TV i (injc (inj i v) SClosed)
    eqPutFclose i v p =
      (λ _ → op (i₂ (i₁ (set inj v
               (op (i₂ (i₂ (fclose getOC (trans (proj-inj i v) p) injc (pure ku)))))))))
      ≐ (λ _ → subst (Free Full TV i) (sym (InjInjComm.inj-comm ic′ i SClosed v))
                 (op (i₂ (i₂ (fclose getOC p injc
                   (op (i₂ (i₁ (set inj v (pure ku))))))))))

    ----------------------------------------------------------------------
    -- Beviser

    eqGetFopen-ok : ∀ i p f
      → respects {Σ = Full} {C = C} ⦃ fFull ⦄ algD (eqGetFopen i p f)
    eqGetFopen-ok i p f ρ t = refl

    eqGetFread-ok : ∀ i p
      → respects {Σ = Full} {C = C} ⦃ fFull ⦄ algD (eqGetFread i p)
    eqGetFread-ok i p ρ t = refl

    eqGetFwrite-ok : ∀ i p t′
      → respects {Σ = Full} {C = C} ⦃ fFull ⦄ algD (eqGetFwrite i p t′)
    eqGetFwrite-ok i p t′ ρ t = refl

    eqGetFclose-ok : ∀ i p
      → respects {Σ = Full} {C = C} ⦃ fFull ⦄ algD (eqGetFclose i p)
    eqGetFclose-ok i p ρ t = refl

    eqPutFopen-ok : ∀ i v p f
      → respects {Σ = Full} {C = C} ⦃ fFull ⦄ algD (eqPutFopen i v p f)
    eqPutFopen-ok i v p f ρ _
      with injₒ (inj i v) SOpen | inj-comm i SOpen v
    ... | .(inj (injₒ i SOpen) v) | refl = refl

    eqPutFread-ok : ∀ i v p
      → respects {Σ = Full} {C = C} ⦃ fFull ⦄ algD (eqPutFread i v p)
    eqPutFread-ok i v p ρ t = refl

    eqPutFwrite-ok : ∀ i v p t′
      → respects {Σ = Full} {C = C} ⦃ fFull ⦄ algD (eqPutFwrite i v p t′)
    eqPutFwrite-ok i v p t′ ρ t = refl

    eqPutFclose-ok : ∀ i v p
      → respects {Σ = Full} {C = C} ⦃ fFull ⦄ algD (eqPutFclose i v p)
    eqPutFclose-ok i v p ρ _
      with injc (inj i v) SClosed | InjInjComm.inj-comm ic′ i SClosed v
    ... | .(inj (injc i SClosed) v) | refl = refl
  module Interactions where

    -- look: fortsættelsen starter i samme tilstand
    module IGet {a : Set} (proj : ProjL I a) (X : Set) =
      G.Inter a i₀
        (λ {K} {j} c → i₁ (look proj c))
        (λ f c → refl) X

    -- set: fortsættelsen starter i inj i₀ v
    module IPut {a : Set} (inj : InjL I a I) (v : a) (X : Set) =
      G.Inter ⊤ (inj i₀ v)
        (λ {K} {j} c → i₁ (set inj v (c tt)))
        (λ f c → refl) X

    -- fopen: kræver getOC i₀ ≡ Closed, fortsættelsen starter i injₒ i₀ SOpen
    module IFopen (getOC : ProjF I) (p : getOC i₀ ≡ Closed)
                  (injₒ : InjF I Open I) (f : String) (X : Set) =
      G.Inter ⊤ (injₒ i₀ SOpen)
        (λ {K} {j} c → i₂ (fopen getOC p injₒ f (c tt)))
        (λ g c → refl) X

    -- fread: kræver getOC i₀ ≡ Open, fortsættelsen får en String
    module IFread (getOC : ProjF I) (p : getOC i₀ ≡ Open) (X : Set) =
      G.Inter String i₀
        (λ {K} {j} c → i₂ (fread getOC p c))
        (λ f c → refl) X

    -- fwrite
    module IFwrite (getOC : ProjF I) (p : getOC i₀ ≡ Open) (s : String) (X : Set) =
      G.Inter ⊤ i₀
        (λ {K} {j} c → i₂ (fwrite getOC p s (c tt)))
        (λ f c → refl) X

    -- fclose: fortsættelsen starter i injc i₀ SClosed
    module IFclose (getOC : ProjF I) (p : getOC i₀ ≡ Open)
                   (injc : InjF I Closed I) (X : Set) =
      G.Inter ⊤ (injc i₀ SClosed)
        (λ {K} {j} c → i₂ (fclose getOC p injc (c tt)))
        (λ f c → refl) X

  -- Kørsel

  genD : A → C j₀ j₀
  genD x = λ hd s m → (just x , s) , m

  -- et throw uden handler giver nothing
  runD : ∀ {i} → Free Full A i j₀ → D i j₀
  runD t = fold {C = C} ⦃ fFull ⦄ genD algD t (λ s s' m → (nothing , s') , m)