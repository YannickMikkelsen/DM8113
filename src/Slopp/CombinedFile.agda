module Slopp.CombinedFile where

open import Data.Unit          using (⊤; tt)
open import Data.Maybe         using (Maybe; just; nothing)
open import Data.String        using (String)
open import Data.Product       using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)

open import Slopp.PHexc
open import Slopp.Lawful
open import Slopp.StateSig
open import Slopp.FHAlg
open import Slopp.PExcGen
open Functor ⦃...⦄

record ⊤₁ : Set₁ where
  constructor tt₁

record ProjInjIndep {I A B : Set} (proj-a : I → A) (inj-b : I → B → I) : Set where
  field proj-inj : ∀ i v → proj-a (inj-b i v) ≡ proj-a i

record InjInjComm {I A B : Set} (inj-a : I → A → I) (inj-b : I → B → I) : Set where
  field inj-comm : ∀ i w v → inj-a (inj-b i v) w ≡ inj-b (inj-a i w) v


-- I er indeksmængden.
module FileAlg (I : Set) (A : Set₁) where

  -- Signatur: state + fil, begge rene indekserede funktorer
  Sg : (I → I → Set₁) → (I → I → Set₁)
  Sg = StateOp {I} + FileOpS {I}

  -- Instanserne gives eksplicit (ingen instance-søgning på Sg og Full, som er
  -- definitioner og derfor får Agda til at sidde fast)
  fSg : Functor Sg
  fSg = Functor+ ⦃ fState ⦄ ⦃ fFile ⦄

  lawfulSg : Lawful Sg ⦃ fSg ⦄
  lawfulSg = lawful+ ⦃ fState ⦄ ⦃ fFile ⦄ lawfulState lawfulFile

  -- Kørselstilstand: den aktuelle tilstand er en værdi af I, og filens
  -- indhold er en String. Indeksene i typerne er statiske og bruges ikke
  -- i kørslen (bæreren er konstant i begge indeks).
  R : Set₁
  R = Maybe A × I

  D : I → Set₁
  D _ = String → R × String

  -- Tilstanden er selve indekset: look læser proj a, set skifter til indeks inj a val.
  αD : ∀ {a j} → Sg (λ i _ → D i) a j → D a
  αD {a} (i₁ (look proj k)) = k (proj a)
  αD (i₁ (set inj val k))   = k
  αD {a} {j} (i₂ f)        = algFile {I} {R} {a} {j} f

  module G = Gen Sg ⦃ fSg ⦄ lawfulSg D αD

  Full : (I → I → Set₁) → (I → I → Set₁)
  Full = G.S              -- = Exc J + (StateOp + FileOpS)

  fFull : Functor Full
  fFull = Functor+ ⦃ fExc ⦄ ⦃ fSg ⦄

  C : I → I → Set₁
  C = G.C

  algD : ∀ {a j} → Full C a j → C a j
  algD = G.algE

  -- fold af et Free-program med generatortolkning gen
  Fd : ∀ {B : Set₁} {j : I} → (B → C j j) → ∀ {i} → Free Full B i j → C i j
  Fd {j = j} gen p = fold {Σ = Full} {C = C} ⦃ fFull ⦄ {j = j} gen algD p

  ----------------------------------------------------------------------
  -- "Variablerne" fra de gamle ligninger er nu programmer i miljøet Γ.
  -- Generatortypen er ⊥₁ (fra Slopp.PExcGen), så alle sider er rene Free-termer.
  --
  --   Ti x : et program, der starter i x og ender i j₀
  --   Tm   : et program for ethvert startindeks x (erstatter "tv : ∀ {x} → …")
  --   Kv X : en fortsættelse, der må starte i ethvert indeks
  
  Ti : I → I → Set₁
  Ti j x = Free Full ⊥₁ x j

  Tm : I → Set₁
  Tm j = (x : I) → Ti j x

  -- Kv : Set → Set₁
  -- Kv X = X → Tm

  ----------------------------------------------------------------------
  -- State-love. Generatorform: pure-blade, Γ = ⊤₁, parametre som argumenter.

  module StateLaws {a : Set} (proj : ProjL I a) (inj : InjL I a I) where
    data SV : Set₁ where
      tv  : SV
      kv  : a → SV
      kv2 : a → a → SV

    -- Look-Discard: look proj (λ _ → t) ≡ t
    eqLookDiscard : (i : I) → Equation Full ⊤₁ SV i i
    eqLookDiscard i =
        (λ _ → op (i₂ (i₁ (look proj (λ _ → pure tv)))))
      ≐ (λ _ → pure tv)

    -- Set-Look: set inj s (look proj (λ s' → kv s')) ≡ set inj s (kv s)
    --   side condition: proj (inj i s) ≡ s
    eqSetLook : (i : I) (s : a) → Equation Full ⊤₁ SV i (inj i s)
    eqSetLook i s =
        (λ _ → op (i₂ (i₁ (set inj s
                 (op (i₂ (i₁ (look proj (λ s' → pure (kv s'))))))))))
      ≐ (λ _ → op (i₂ (i₁ (set inj s (pure (kv s))))))

    -- Look-Set: look proj (λ s → set inj s t) ≡ t
    --   side condition: inj i (proj i) ≡ i
    -- eqLookSet : (i : I) → Equation Full Tm ⊥₁ i j₀
    -- eqLookSet i =
    --     (λ t → op (i₂ (i₁ (look proj (λ s →
    --               op (i₂ (i₁ (set inj s (t (inj i s))))))))))
    --   ≐ (λ t → t i)
    -- Look-Set kan IKKE skrives med pure-blad: set inj s ender i inj i s,
    -- som afhænger af s, mens look kræver ét fast slutindeks. Derfor står
    -- den i t-formen (fortsættelsen t i Γ).
    -- side condition: inj i (proj i) ≡ i
    eqLookSet : (i j : I) → Equation Full (Tm j) ⊥₁ i j
    eqLookSet i j =
        (λ t → op (i₂ (i₁ (look proj (λ s →
                 op (i₂ (i₁ (set inj s (t (inj i s))))))))))
      ≐ (λ t → t i)

    -- Look-Look: look proj (λ s → look proj (λ s' → kv2 s s')) ≡ look proj (λ s → kv2 s s)
    eqLookLook : (i : I) → Equation Full ⊤₁ SV i i
    eqLookLook i =
        (λ _ → op (i₂ (i₁ (look proj (λ s →
                 op (i₂ (i₁ (look proj (λ s' → pure (kv2 s s'))))))))))
      ≐ (λ _ → op (i₂ (i₁ (look proj (λ s → pure (kv2 s s))))))


    -- Set-Set: set inj s₁ (set inj s₂ t) ≡ set inj s₂ t
    --   side condition: inj (inj i s₁) s₂ ≡ inj i s₂
    -- eqSetSet : (i : I) → Equation Full ((a × a) × Tm) ⊥₁ i j₀
    -- eqSetSet i =
    --     (λ { ((s₁ , s₂) , t) → op (i₂ (i₁ (set inj s₁
    --                              (op (i₂ (i₁ (set inj s₂ (t (inj (inj i s₁) s₂))))))))) })
    --   ≐ (λ { ((_ , s₂) , t) → op (i₂ (i₁ (set inj s₂ (t (inj i s₂))))) })
    eqSetSet : (i : I) (s₁ s₂ : a) → inj (inj i s₁) s₂ ≡ inj i s₂
             → Equation Full ⊤₁ SV i (inj (inj i s₁) s₂)
    eqSetSet i s₁ s₂ coh =
        (λ _ → op (i₂ (i₁ (set inj s₁ (op (i₂ (i₁ (set inj s₂ (pure tv)))))))))
      ≐ (λ _ → subst (Free Full SV i) (sym coh)
                 (op (i₂ (i₁ (set inj s₂ (pure tv))))))

    ----------------------------------------------------------------------
    -- Typer på beviserne. Side conditions tages for alle køretidstilstande st,
    -- fordi D bruger I som tilstand.

    eqLookDiscard-ok : ∀ i
      → respects {Σ = Full} {C = C} ⦃ fFull ⦄ algD (eqLookDiscard i)
    eqLookDiscard-ok i gen _ = refl

    -- eqSetLook-ok : ∀ i
    --   → (∀ st s → proj (inj st s) ≡ s)
    --   → respects {Σ = Full} {C = C} ⦃ fFull ⦄ algD (eqSetLook i)
    -- eqSetLook-ok i coh gen (s , kv) =
    --   funext (λ hd →
    --     cong (λ x → Fd gen (kv x (inj i s)) hd) (coh i s))
    eqSetLook-ok : ∀ i s
      → proj (inj i s) ≡ s
      → respects {Σ = Full} {C = C} ⦃ fFull ⦄ algD (eqSetLook i s)
    eqSetLook-ok i s coh gen _ =
      funext (λ hd → cong (λ x → gen (kv x) hd) coh)

    -- Get-Put: set skriver det, look læste, tilbage i indekset i.
    -- eqLookSet-ok : ∀ i
    --   → (inj i (proj i) ≡ i)
    --   → respects {Σ = Full} {C = C} ⦃ fFull ⦄ algD (eqLookSet i)
    -- eqLookSet-ok i coh-i gen t =
    --   funext (λ hd → cong (λ n → Fd gen (t n) hd) coh-i)
    eqLookSet-ok : ∀ i j
      → inj i (proj i) ≡ i
      → respects {Σ = Full} {C = C} ⦃ fFull ⦄ algD (eqLookSet i j)
    eqLookSet-ok i j coh gen t =
      funext (λ hd → cong (λ n → Fd gen (t n) hd) coh)

    eqLookLook-ok : ∀ i
      → respects {Σ = Full} {C = C} ⦃ fFull ⦄ algD (eqLookLook i)
    eqLookLook-ok i gen _ = refl

    -- eqSetSet-ok : ∀ i
    --   → (∀ st s₁ s₂ → inj (inj st s₁) s₂ ≡ inj st s₂)
    --   → respects {Σ = Full} {C = C} ⦃ fFull ⦄ algD (eqSetSet i)
    -- eqSetSet-ok i coh gen ((s₁ , s₂) , t) =
    --   funext (λ hd →
    --     cong (λ n → Fd gen (t n) hd) (coh i s₁ s₂))

    eqSetSet-ok : ∀ i s₁ s₂ (coh : inj (inj i s₁) s₂ ≡ inj i s₂)
        → respects {Σ = Full} {C = C} ⦃ fFull ⦄ algD (eqSetSet i s₁ s₂ coh)
    eqSetSet-ok i s₁ s₂ coh gen _ with inj (inj i s₁) s₂ | coh
    ... | .(inj i s₂) | refl = refl
  ----------------------------------------------------------------------
  -- Fil-love. Operationerne ligger i i₂ (i₂ ...) af Full.
  -- Premisserne p : getOC i ≡ Open osv. tages som argumenter til ligningen,
  -- fordi de indgår i typen af fread/fwrite/fopen/fclose.

  module FileLaws where

    data FV : Set₁ where
      tt′ : FV
      kr  : String → FV
      kr2 : String → String → FV

    -- Open-Close: fopen getOCₒ pₒ injₒ f (fclose getOC꜀ p꜀ inj꜀ t) ≡ t
    --   side condition: inj꜀ (injₒ i SOpen) SClosed ≡ i
    -- eqOpenClose : (i : I)
    --               (getOCₒ getOC꜀ : ProjF I)
    --               (pₒ : getOCₒ i ≡ Closed)
    --               (injₒ : InjF I Open I)
    --               (p꜀ : getOC꜀ (injₒ i SOpen) ≡ Open)
    --               (inj꜀ : InjF I Closed I)
    --             → Equation Full (String × Tm) ⊥₁ i j₀
    -- eqOpenClose i getOCₒ getOC꜀ pₒ injₒ p꜀ inj꜀ =
    --     (λ { (f , t) → op (i₂ (i₂ (fopen getOCₒ pₒ injₒ f
    --                      (op (i₂ (i₂ (fclose getOC꜀ p꜀ inj꜀
    --                         (t (inj꜀ (injₒ i SOpen) SClosed))))))))) })
    --   ≐ (λ { (_ , t) → t i })

    eqOpenClose : (i : I) (getOCₒ getOC꜀ : ProjF I)
                  (pₒ : getOCₒ i ≡ Closed) (injₒ : InjF I Open I)
                  (p꜀ : getOC꜀ (injₒ i SOpen) ≡ Open) (inj꜀ : InjF I Closed I)
                  (f : String)
                → inj꜀ (injₒ i SOpen) SClosed ≡ i
                → Equation Full ⊤₁ FV i (inj꜀ (injₒ i SOpen) SClosed)
    eqOpenClose i getOCₒ getOC꜀ pₒ injₒ p꜀ inj꜀ f coh =
        (λ _ → op (i₂ (i₂ (fopen getOCₒ pₒ injₒ f
                 (op (i₂ (i₂ (fclose getOC꜀ p꜀ inj꜀ (pure tt′)))))))))
      ≐ (λ _ → subst (Free Full FV i) (sym coh) (pure tt′))

    -- Write-Write: fwrite s₁ (fwrite s₂ t) ≡ fwrite s₂ t
    eqWriteWrite : (i : I) (getOC : ProjF I) (p : getOC i ≡ Open) (s₁ s₂ : String)
                 → Equation Full ⊤₁ FV i i
    eqWriteWrite i getOC p s₁ s₂ =
        (λ _ → op (i₂ (i₂ (fwrite getOC p s₁
                 (op (i₂ (i₂ (fwrite getOC p s₂ (pure tt′)))))))))
      ≐ (λ _ → op (i₂ (i₂ (fwrite getOC p s₂ (pure tt′)))))

    -- Write-Read: fwrite s (fread (λ r → kr r)) ≡ fwrite s (kr s)
    eqWriteRead : (i : I) (getOC : ProjF I) (p : getOC i ≡ Open) (s : String)
                → Equation Full ⊤₁ FV i i
    eqWriteRead i getOC p s =
        (λ _ → op (i₂ (i₂ (fwrite getOC p s
                 (op (i₂ (i₂ (fread getOC p (λ r → pure (kr r))))))))))
      ≐ (λ _ → op (i₂ (i₂ (fwrite getOC p s (pure (kr s))))))

      
    -- Read-Discard: fread (λ _ → t) ≡ t
    eqReadDiscard : (i : I) (getOC : ProjF I) (p : getOC i ≡ Open)
                  → Equation Full ⊤₁ FV i i
    eqReadDiscard i getOC p =
        (λ _ → op (i₂ (i₂ (fread getOC p (λ _ → pure tt′)))))
      ≐ (λ _ → pure tt′)

    -- Read-Write: fread (λ s → fwrite s t) ≡ t
    eqReadWrite : (i : I) (getOC : ProjF I) (p : getOC i ≡ Open)
                → Equation Full ⊤₁ FV i i
    eqReadWrite i getOC p =
        (λ _ → op (i₂ (i₂ (fread getOC p (λ s →
                 op (i₂ (i₂ (fwrite getOC p s (pure tt′)))))))))
      ≐ (λ _ → pure tt′)

    -- Read-Read: fread (λ s → fread (λ s' → kr2 s s')) ≡ fread (λ s → kr2 s s)
    eqReadRead : (i : I) (getOC : ProjF I) (p : getOC i ≡ Open)
               → Equation Full ⊤₁ FV i i
    eqReadRead i getOC p =
        (λ _ → op (i₂ (i₂ (fread getOC p (λ s →
                 op (i₂ (i₂ (fread getOC p (λ s' → pure (kr2 s s'))))))))))
      ≐ (λ _ → op (i₂ (i₂ (fread getOC p (λ s → pure (kr2 s s))))))

    ----------------------------------------------------------------------
    -- Typer på beviserne

    eqOpenClose-ok : ∀ i getOCₒ getOC꜀ pₒ injₒ p꜀ inj꜀ f
      → (coh : inj꜀ (injₒ i SOpen) SClosed ≡ i)
      → respects {Σ = Full} {C = C} ⦃ fFull ⦄ algD
                 (eqOpenClose i getOCₒ getOC꜀ pₒ injₒ p꜀ inj꜀ f coh)
    eqOpenClose-ok i getOCₒ getOC꜀ pₒ injₒ p꜀ inj꜀ f coh gen _
      with inj꜀ (injₒ i SOpen) SClosed | coh
    ... | .i | refl = refl

    eqWriteWrite-ok : ∀ i getOC p s₁ s₂
      → respects {Σ = Full} {C = C} ⦃ fFull ⦄ algD (eqWriteWrite i getOC p s₁ s₂)
    eqWriteWrite-ok i getOC p s₁ s₂ gen _ = refl

    eqWriteRead-ok : ∀ i getOC p s
      → respects {Σ = Full} {C = C} ⦃ fFull ⦄ algD (eqWriteRead i getOC p s)
    eqWriteRead-ok i getOC p s gen _ = refl

    eqReadDiscard-ok : ∀ i getOC p
      → respects {Σ = Full} {C = C} ⦃ fFull ⦄ algD (eqReadDiscard i getOC p)
    eqReadDiscard-ok i getOC p gen _ = refl

    eqReadWrite-ok : ∀ i getOC p
      → respects {Σ = Full} {C = C} ⦃ fFull ⦄ algD (eqReadWrite i getOC p)
    eqReadWrite-ok i getOC p gen _ = refl

    eqReadRead-ok : ∀ i getOC p
      → respects {Σ = Full} {C = C} ⦃ fFull ⦄ algD (eqReadRead i getOC p)
    eqReadRead-ok i getOC p gen _ = refl

  module TensorLaws {a : Set} (proj : ProjL I a) (inj : InjL I a I)
                    (getOC : ProjF I) (injₒ : InjF I Open I) (injc : InjF I Closed I)
                    (pi : ProjInjIndep getOC inj) (ic : InjInjComm injₒ inj) (ic′ : InjInjComm injc inj)
                    (pio : ProjInjIndep proj injₒ) (pic : ProjInjIndep proj injc) where

    open ProjInjIndep pi
    open InjInjComm ic

    data TV : Set₁ where
      ka : a → TV
      kb : a → String → TV
      kr : String → TV
      ku : TV

    ----------------------------------------------------------------------
    

    -- Get-Fopen
    eqGetFopen : (i : I) (p : getOC i ≡ Closed) (f : String)
               → Equation Full ⊤₁ TV i (injₒ i SOpen)
    eqGetFopen i p f =
        (λ _ → op (i₂ (i₁ (look proj (λ s →
                 op (i₂ (i₂ (fopen getOC p injₒ f (pure (ka s))))))))))
      ≐ (λ _ → op (i₂ (i₂ (fopen getOC p injₒ f
                 (op (i₂ (i₁ (look proj (λ s → pure (ka s))))))))))

    -- Get-Fread
    eqGetFread : (i : I) (p : getOC i ≡ Open) → Equation Full ⊤₁ TV i i
    eqGetFread i p =
        (λ _ → op (i₂ (i₁ (look proj (λ s →
                 op (i₂ (i₂ (fread getOC p (λ r → pure (kb s r))))))))))
      ≐ (λ _ → op (i₂ (i₂ (fread getOC p (λ r →
                 op (i₂ (i₁ (look proj (λ s → pure (kb s r))))))))))

    -- Get-Fwrite
    eqGetFwrite : (i : I) (p : getOC i ≡ Open) (t : String) → Equation Full ⊤₁ TV i i
    eqGetFwrite i p t =
        (λ _ → op (i₂ (i₁ (look proj (λ s →
                 op (i₂ (i₂ (fwrite getOC p t (pure (ka s))))))))))
      ≐ (λ _ → op (i₂ (i₂ (fwrite getOC p t
                 (op (i₂ (i₁ (look proj (λ s → pure (ka s))))))))))

    -- Get-Fclose
    eqGetFclose : (i : I) (p : getOC i ≡ Open)
                → Equation Full ⊤₁ TV i (injc i SClosed)
    eqGetFclose i p =
        (λ _ → op (i₂ (i₁ (look proj (λ s →
                 op (i₂ (i₂ (fclose getOC p injc (pure (ka s))))))))))
      ≐ (λ _ → op (i₂ (i₂ (fclose getOC p injc
                 (op (i₂ (i₁ (look proj (λ s → pure (ka s))))))))))


    ----------------------------------------------------------------------
   

    -- Put-Fopen
    eqPutFopen : (i : I) (v : a) (p : getOC i ≡ Closed) (f : String)
               → Equation Full ⊤₁ TV i (injₒ (inj i v) SOpen)
    eqPutFopen i v p f =
        (λ _ → op (i₂ (i₁ (set inj v
                 (op (i₂ (i₂ (fopen getOC (trans (proj-inj i v) p) injₒ f
                                    (pure ku)))))))))
      ≐ (λ _ → subst (Free Full TV i) (sym (inj-comm i SOpen v))
                 (op (i₂ (i₂ (fopen getOC p injₒ f
                   (op (i₂ (i₁ (set inj v (pure ku))))))))))

    -- Put-Fread
    eqPutFread : (i : I) (v : a) (p : getOC i ≡ Open)
               → Equation Full ⊤₁ TV i (inj i v)
    eqPutFread i v p =
        (λ _ → op (i₂ (i₁ (set inj v
                 (op (i₂ (i₂ (fread getOC (trans (proj-inj i v) p)
                                    (λ r → pure (kr r))))))))))
      ≐ (λ _ → op (i₂ (i₂ (fread getOC p (λ r →
                 op (i₂ (i₁ (set inj v (pure (kr r))))))))))


    -- Put-Fwrite
    eqPutFwrite : (i : I) (v : a) (p : getOC i ≡ Open) (t : String)
                → Equation Full ⊤₁ TV i (inj i v)
    eqPutFwrite i v p t =
        (λ _ → op (i₂ (i₁ (set inj v
                 (op (i₂ (i₂ (fwrite getOC (trans (proj-inj i v) p) t (pure ku)))))))))
      ≐ (λ _ → op (i₂ (i₂ (fwrite getOC p t
                 (op (i₂ (i₁ (set inj v (pure ku)))))))))

    -- Put-Fclose
    eqPutFclose : (i : I) (v : a) (p : getOC i ≡ Open)
                → Equation Full ⊤₁ TV i (injc (inj i v) SClosed)
    eqPutFclose i v p =
        (λ _ → op (i₂ (i₁ (set inj v
                 (op (i₂ (i₂ (fclose getOC (trans (proj-inj i v) p) injc
                                     (pure ku)))))))))
      ≐ (λ _ → subst (Free Full TV i) (sym (InjInjComm.inj-comm ic′ i SClosed v))
                 (op (i₂ (i₂ (fclose getOC p injc
                   (op (i₂ (i₁ (set inj v (pure ku))))))))))
    ----------------------------------------------------------------------
    -- Typer på beviserne

    eqGetFopen-ok : ∀ i p f
      → respects {Σ = Full} {C = C} ⦃ fFull ⦄ algD (eqGetFopen i p f)
    -- højresiden læser i indeks injₒ i SOpen, så proj skal være uafhængig af injₒ
    eqGetFopen-ok i p f gen _ =
      funext (λ hd → cong (λ s → gen (ka s) hd) (sym (ProjInjIndep.proj-inj pio i SOpen)))

    eqGetFread-ok : ∀ i p
      → respects {Σ = Full} {C = C} ⦃ fFull ⦄ algD (eqGetFread i p)
    eqGetFread-ok i p gen _ = refl

    eqGetFwrite-ok : ∀ i p t′
      → respects {Σ = Full} {C = C} ⦃ fFull ⦄ algD (eqGetFwrite i p t′)
    eqGetFwrite-ok i p t′ gen _ = refl

    eqGetFclose-ok : ∀ i p
      → respects {Σ = Full} {C = C} ⦃ fFull ⦄ algD (eqGetFclose i p)
    eqGetFclose-ok i p gen _ =
      funext (λ hd → cong (λ s → gen (ka s) hd) (sym (ProjInjIndep.proj-inj pic i SClosed)))

    eqPutFopen-ok : ∀ i v p f
      → respects {Σ = Full} {C = C} ⦃ fFull ⦄ algD (eqPutFopen i v p f)
    eqPutFopen-ok i v p f gen _
      with injₒ (inj i v) SOpen | inj-comm i SOpen v
    ... | .(inj (injₒ i SOpen) v) | refl = refl

    eqPutFread-ok : ∀ i v p
      → respects {Σ = Full} {C = C} ⦃ fFull ⦄ algD (eqPutFread i v p)
    eqPutFread-ok i v p gen _ = refl

    eqPutFwrite-ok : ∀ i v p t′
      → respects {Σ = Full} {C = C} ⦃ fFull ⦄ algD (eqPutFwrite i v p t′)
    eqPutFwrite-ok i v p t′ gen _ = refl

    eqPutFclose-ok : ∀ i v p
      → respects {Σ = Full} {C = C} ⦃ fFull ⦄ algD (eqPutFclose i v p)
    eqPutFclose-ok i v p gen _
      with injc (inj i v) SClosed | InjInjComm.inj-comm ic′ i SClosed v
    ... | .(inj (injc i SClosed) v) | refl = refl


  module Interactions where

    -- look: fortsættelsen starter i samme tilstand
    module IGet {a : Set} (proj : ProjL I a) (i m j : I) (X : Set) =
      G.Inter a i i m j
        (λ {K} {j'} c → i₁ (look proj c))
        (λ f c → refl) X

    -- set: fortsættelsen starter i inj i₀ v
    module IPut {a : Set} (inj : InjL I a I) (v : a) (i m j : I) (X : Set) =
      G.Inter ⊤ i (inj i v) m j
        (λ {K} {j'} c → i₁ (set inj v (c tt)))
        (λ f c → refl) X

    -- fopen: kræver getOC i₀ ≡ Closed, fortsættelsen starter i injₒ i₀ SOpen
    module IFopen (getOC : ProjF I) (i : I) (p : getOC i ≡ Closed)
                  (injₒ : InjF I Open I) (f : String) (m j : I) (X : Set) =
      G.Inter ⊤ i (injₒ i SOpen) m j
        (λ {K} {j'} c → i₂ (fopen getOC p injₒ f (c tt)))
        (λ g c → refl) X

    -- fread: kræver getOC i₀ ≡ Open, fortsættelsen får en String
    module IFread (getOC : ProjF I) (i : I) (p : getOC i ≡ Open) (m j : I) (X : Set) =
      G.Inter String i i m j
        (λ {K} {j'} c → i₂ (fread getOC p c))
        (λ f c → refl) X

    -- fwrite
    module IFwrite (getOC : ProjF I) (i : I) (p : getOC i ≡ Open) (s : String)
                   (m j : I) (X : Set) =
      G.Inter ⊤ i i m j
        (λ {K} {j'} c → i₂ (fwrite getOC p s (c tt)))
        (λ f c → refl) X

    -- fclose: fortsættelsen starter i injc i₀ SClosed
    module IFclose (getOC : ProjF I) (i : I) (p : getOC i ≡ Open)
                   (injc : InjF I Closed I) (m j : I) (X : Set) =
      G.Inter ⊤ i (injc i SClosed) m j
        (λ {K} {j'} c → i₂ (fclose getOC p injc (c tt)))
        (λ f c → refl) X
--   -- Kørsel

  genD : ∀ {j} → A → C j j
  genD {j} x = λ hd m → (just x , j) , m

  -- et throw uden handler giver nothing (sluttilstanden er fejlindekset s)
  runD : ∀ {i j} → Free Full A i j → D i
  runD {j = j} t = fold {C = C} ⦃ fFull ⦄ {j = j} (genD {j = j}) algD t (λ s m → (nothing , s) , m)