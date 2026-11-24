-- {-# OPTIONS --allow-unsolved-metas #-}
module Slopp.CombinedFile where

-- Parameterized udgave: state + fil kombineres, og Gen (Exc-delen) lægges
-- ovenpå. IKKE typechecket. Lovene bevises bagefter.
-- Alle ligninger er nu kun udtrykt med Free (ingen Term/var/opT).

open import Data.Unit          using (⊤; tt)
open import Data.Maybe         using (Maybe; just; nothing)
open import Data.String        using (String)
open import Data.Product       using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)

open import Slopp.PHexc
open import Slopp.Lawful
open import Slopp.StateSig
open import Slopp.FHAlg
open import Slopp.PExcGen
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

  D : I → I → Set₁
  D i j = HF {I} R i j

  -- Tilstanden er selve indekset: look læser proj a, set skifter til indeks inj a val.
  αD : ∀ {a} → Sg D a j₀ → D a j₀
  αD {a} (i₁ (look proj k))   = k (proj a)
  αD (i₁ (set inj val k))     = k
  αD (i₂ f)                   = algFile (fmap ⦃ fFile ⦄ {X = D} {Y = HF {I} R} {j = j₀} {j' = j₀}
                                              (λ {i} k → k) f)

  module G = Gen Sg ⦃ fSg ⦄ lawfulSg i₀ j₀ k₀ m₀ D αD

  Full : (I → I → Set₁) → (I → I → Set₁)
  Full = G.S              -- = Exc J + (StateOp + FileOpS)

  fFull : Functor Full
  fFull = Functor+ ⦃ fExc ⦄ ⦃ fSg ⦄

  C : I → I → Set₁
  C = G.C

  algD : ∀ {a} → Full C a j₀ → C a j₀
  algD = G.algE

  -- fold af et Free-program med generatortolkning gen
  Fd : ∀ {B : Set₁} → (B → C j₀ j₀) → ∀ {i} → Free Full B i j₀ → C i j₀
  Fd gen p = fold {Σ = Full} {C = C} ⦃ fFull ⦄ {j = j₀} gen algD p

  ----------------------------------------------------------------------
  -- "Variablerne" fra de gamle ligninger er nu programmer i miljøet Γ.
  -- Generatortypen er ⊥₁ (fra Slopp.PExcGen), så alle sider er rene Free-termer.
  --
  --   Ti x : et program, der starter i x og ender i j₀
  --   Tm   : et program for ethvert startindeks x (erstatter "tv : ∀ {x} → …")
  --   Kv X : en fortsættelse, der må starte i ethvert indeks

  Ti : I → Set₁
  Ti x = Free Full ⊥₁ x j₀

  Tm : Set₁
  Tm = (x : I) → Ti x

  Kv : Set → Set₁
  Kv X = X → Tm

  ----------------------------------------------------------------------
  -- State-love.

  module StateLaws {a : Set} (proj : ProjL I a) (inj : InjL I a I) where

    -- Look-Discard: look proj (λ _ → t) ≡ t
    eqLookDiscard : (i : I) → Equation Full (Ti i) ⊥₁ i j₀
    eqLookDiscard i =
        (λ t → op (i₂ (i₁ (look proj (λ _ → t)))))
      ≐ (λ t → t)

    -- Set-Look: set inj s (look proj (λ s' → kv s')) ≡ set inj s (kv s)
    --   side condition: proj (inj i s) ≡ s
    eqSetLook : (i : I) → Equation Full (a × Kv a) ⊥₁ i j₀
    eqSetLook i =
        (λ { (s , kv) → op (i₂ (i₁ (set inj s
                          (op (i₂ (i₁ (look proj (λ s' → kv s' (inj i s))))))))) })
      ≐ (λ { (s , kv) → op (i₂ (i₁ (set inj s (kv s (inj i s))))) })

    -- Look-Set: look proj (λ s → set inj s t) ≡ t
    --   side condition: inj i (proj i) ≡ i
    eqLookSet : (i : I) → Equation Full Tm ⊥₁ i j₀
    eqLookSet i =
        (λ t → op (i₂ (i₁ (look proj (λ s →
                  op (i₂ (i₁ (set inj s (t (inj i s))))))))))
      ≐ (λ t → t i)

    -- Look-Look: look proj (λ s → look proj (λ s' → kv2 s s')) ≡ look proj (λ s → kv2 s s)
    eqLookLook : (i : I) → Equation Full (a → a → Ti i) ⊥₁ i j₀
    eqLookLook i =
        (λ kv2 → op (i₂ (i₁ (look proj (λ s →
                   op (i₂ (i₁ (look proj (λ s' → kv2 s s')))))))))
      ≐ (λ kv2 → op (i₂ (i₁ (look proj (λ s → kv2 s s)))))

    -- Set-Set: set inj s₁ (set inj s₂ t) ≡ set inj s₂ t
    --   side condition: inj (inj i s₁) s₂ ≡ inj i s₂
    eqSetSet : (i : I) → Equation Full ((a × a) × Tm) ⊥₁ i j₀
    eqSetSet i =
        (λ { ((s₁ , s₂) , t) → op (i₂ (i₁ (set inj s₁
                                 (op (i₂ (i₁ (set inj s₂ (t (inj (inj i s₁) s₂))))))))) })
      ≐ (λ { ((_ , s₂) , t) → op (i₂ (i₁ (set inj s₂ (t (inj i s₂))))) })

    ----------------------------------------------------------------------
    -- Typer på beviserne. Side conditions tages for alle køretidstilstande st,
    -- fordi D bruger I som tilstand.

    eqLookDiscard-ok : ∀ i
      → respects {Σ = Full} {C = C} ⦃ fFull ⦄ algD (eqLookDiscard i)
    eqLookDiscard-ok i gen t = refl

    eqSetLook-ok : ∀ i
      → (∀ st s → proj (inj st s) ≡ s)
      → respects {Σ = Full} {C = C} ⦃ fFull ⦄ algD (eqSetLook i)
    eqSetLook-ok i coh gen (s , kv) =
      funext (λ hd →
        cong (λ x → Fd gen (kv x (inj i s)) hd) (coh i s))

    -- Get-Put: set skriver det, look læste, tilbage i indekset i.
    eqLookSet-ok : ∀ i
      → (inj i (proj i) ≡ i)
      → respects {Σ = Full} {C = C} ⦃ fFull ⦄ algD (eqLookSet i)
    eqLookSet-ok i coh-i gen t =
      funext (λ hd → cong (λ n → Fd gen (t n) hd) coh-i)

    eqLookLook-ok : ∀ i
      → respects {Σ = Full} {C = C} ⦃ fFull ⦄ algD (eqLookLook i)
    eqLookLook-ok i gen kv2 = refl

    eqSetSet-ok : ∀ i
      → (∀ st s₁ s₂ → inj (inj st s₁) s₂ ≡ inj st s₂)
      → respects {Σ = Full} {C = C} ⦃ fFull ⦄ algD (eqSetSet i)
    eqSetSet-ok i coh gen ((s₁ , s₂) , t) =
      funext (λ hd →
        cong (λ n → Fd gen (t n) hd) (coh i s₁ s₂))

  ----------------------------------------------------------------------
  -- Fil-love. Operationerne ligger i i₂ (i₂ ...) af Full.
  -- Premisserne p : getOC i ≡ Open osv. tages som argumenter til ligningen,
  -- fordi de indgår i typen af fread/fwrite/fopen/fclose.

  module FileLaws where

    -- Open-Close: fopen getOCₒ pₒ injₒ f (fclose getOC꜀ p꜀ inj꜀ t) ≡ t
    --   side condition: inj꜀ (injₒ i SOpen) SClosed ≡ i
    eqOpenClose : (i : I)
                  (getOCₒ getOC꜀ : ProjF I)
                  (pₒ : getOCₒ i ≡ Closed)
                  (injₒ : InjF I Open I)
                  (p꜀ : getOC꜀ (injₒ i SOpen) ≡ Open)
                  (inj꜀ : InjF I Closed I)
                → Equation Full (String × Tm) ⊥₁ i j₀
    eqOpenClose i getOCₒ getOC꜀ pₒ injₒ p꜀ inj꜀ =
        (λ { (f , t) → op (i₂ (i₂ (fopen getOCₒ pₒ injₒ f
                         (op (i₂ (i₂ (fclose getOC꜀ p꜀ inj꜀
                            (t (inj꜀ (injₒ i SOpen) SClosed))))))))) })
      ≐ (λ { (_ , t) → t i })

    -- Write-Write: fwrite s₁ (fwrite s₂ t) ≡ fwrite s₂ t
    eqWriteWrite : (i : I) (getOC : ProjF I) (p : getOC i ≡ Open)
                 → Equation Full ((String × String) × Ti i) ⊥₁ i j₀
    eqWriteWrite i getOC p =
        (λ { ((s₁ , s₂) , t) → op (i₂ (i₂ (fwrite getOC p s₁
                                 (op (i₂ (i₂ (fwrite getOC p s₂ t))))))) })
      ≐ (λ { ((_ , s₂) , t) → op (i₂ (i₂ (fwrite getOC p s₂ t))) })

    -- Write-Read: fwrite s (fread (λ r → kr r)) ≡ fwrite s (kr s)
    eqWriteRead : (i : I) (getOC : ProjF I) (p : getOC i ≡ Open)
                → Equation Full (String × (String → Ti i)) ⊥₁ i j₀
    eqWriteRead i getOC p =
        (λ { (s , kr) → op (i₂ (i₂ (fwrite getOC p s
                          (op (i₂ (i₂ (fread getOC p (λ r → kr r)))))))) })
      ≐ (λ { (s , kr) → op (i₂ (i₂ (fwrite getOC p s (kr s)))) })

    -- Read-Discard: fread (λ _ → t) ≡ t
    eqReadDiscard : (i : I) (getOC : ProjF I) (p : getOC i ≡ Open)
                  → Equation Full (Ti i) ⊥₁ i j₀
    eqReadDiscard i getOC p =
        (λ t → op (i₂ (i₂ (fread getOC p (λ _ → t)))))
      ≐ (λ t → t)

    -- Read-Write: fread (λ s → fwrite s t) ≡ t
    eqReadWrite : (i : I) (getOC : ProjF I) (p : getOC i ≡ Open)
                → Equation Full (Ti i) ⊥₁ i j₀
    eqReadWrite i getOC p =
        (λ t → op (i₂ (i₂ (fread getOC p (λ s →
                 op (i₂ (i₂ (fwrite getOC p s t))))))))
      ≐ (λ t → t)

    -- Read-Read: fread (λ s → fread (λ s' → kr2 s s')) ≡ fread (λ s → kr2 s s)
    eqReadRead : (i : I) (getOC : ProjF I) (p : getOC i ≡ Open)
               → Equation Full (String → String → Ti i) ⊥₁ i j₀
    eqReadRead i getOC p =
        (λ kr2 → op (i₂ (i₂ (fread getOC p (λ s →
                   op (i₂ (i₂ (fread getOC p (λ s' → kr2 s s')))))))))
      ≐ (λ kr2 → op (i₂ (i₂ (fread getOC p (λ s → kr2 s s)))))

    ----------------------------------------------------------------------
    -- Typer på beviserne

    eqOpenClose-ok : ∀ i getOCₒ getOC꜀ pₒ injₒ p꜀ inj꜀
      → (inj꜀ (injₒ i SOpen) SClosed ≡ i)
      → respects {Σ = Full} {C = C} ⦃ fFull ⦄ algD
                 (eqOpenClose i getOCₒ getOC꜀ pₒ injₒ p꜀ inj꜀)
    eqOpenClose-ok i getOCₒ getOC꜀ pₒ injₒ p꜀ inj꜀ coh gen (f , t) =
      funext (λ hb → cong (λ n → Fd gen (t n) hb) coh)

    eqWriteWrite-ok : ∀ i getOC p
      → respects {Σ = Full} {C = C} ⦃ fFull ⦄ algD (eqWriteWrite i getOC p)
    eqWriteWrite-ok i getOC p gen ((s₁ , s₂) , t) = refl

    eqWriteRead-ok : ∀ i getOC p
      → respects {Σ = Full} {C = C} ⦃ fFull ⦄ algD (eqWriteRead i getOC p)
    eqWriteRead-ok i getOC p gen (s , kr) = refl

    eqReadDiscard-ok : ∀ i getOC p
      → respects {Σ = Full} {C = C} ⦃ fFull ⦄ algD (eqReadDiscard i getOC p)
    eqReadDiscard-ok i getOC p gen t = refl

    eqReadWrite-ok : ∀ i getOC p
      → respects {Σ = Full} {C = C} ⦃ fFull ⦄ algD (eqReadWrite i getOC p)
    eqReadWrite-ok i getOC p gen t = refl

    eqReadRead-ok : ∀ i getOC p
      → respects {Σ = Full} {C = C} ⦃ fFull ⦄ algD (eqReadRead i getOC p)
    eqReadRead-ok i getOC p gen kr2 = refl

  module TensorLaws {a : Set} (proj : ProjL I a) (inj : InjL I a I)
                    (getOC : ProjF I) (injₒ : InjF I Open I) (injc : InjF I Closed I)
                    (pi : ProjInjIndep getOC inj) (ic : InjInjComm injₒ inj) (ic′ : InjInjComm injc inj)
                    (pio : ProjInjIndep proj injₒ) (pic : ProjInjIndep proj injc) where

    open ProjInjIndep pi
    open InjInjComm ic

    ----------------------------------------------------------------------
    -- Get × File: look ændrer ikke indekset, så præbetingelsen p bruges direkte,
    -- og begge sider ender i samme indeks (fortsættelsen er et Ti-program).

    -- Get-Fopen
    eqGetFopen : (i : I) (p : getOC i ≡ Closed) (f : String)
               → Equation Full (a → Ti (injₒ i SOpen)) ⊥₁ i j₀
    eqGetFopen i p f =
        (λ ka → op (i₂ (i₁ (look proj (λ s →
                  op (i₂ (i₂ (fopen getOC p injₒ f (ka s)))))))))
      ≐ (λ ka → op (i₂ (i₂ (fopen getOC p injₒ f
                  (op (i₂ (i₁ (look proj (λ s → ka s)))))))))

    -- Get-Fread
    eqGetFread : (i : I) (p : getOC i ≡ Open)
               → Equation Full (a → String → Ti i) ⊥₁ i j₀
    eqGetFread i p =
        (λ kb → op (i₂ (i₁ (look proj (λ s →
                  op (i₂ (i₂ (fread getOC p (λ r → kb s r)))))))))
      ≐ (λ kb → op (i₂ (i₂ (fread getOC p (λ r →
                  op (i₂ (i₁ (look proj (λ s → kb s r)))))))))

    -- Get-Fwrite
    eqGetFwrite : (i : I) (p : getOC i ≡ Open) (t : String)
                → Equation Full (a → Ti i) ⊥₁ i j₀
    eqGetFwrite i p t =
        (λ ka → op (i₂ (i₁ (look proj (λ s →
                  op (i₂ (i₂ (fwrite getOC p t (ka s)))))))))
      ≐ (λ ka → op (i₂ (i₂ (fwrite getOC p t
                  (op (i₂ (i₁ (look proj (λ s → ka s)))))))))

    -- Get-Fclose
    eqGetFclose : (i : I) (p : getOC i ≡ Open)
                → Equation Full (a → Ti (injc i SClosed)) ⊥₁ i j₀
    eqGetFclose i p =
        (λ ka → op (i₂ (i₁ (look proj (λ s →
                  op (i₂ (i₂ (fclose getOC p injc (ka s)))))))))
      ≐ (λ ka → op (i₂ (i₂ (fclose getOC p injc
                  (op (i₂ (i₁ (look proj (λ s → ka s)))))))))

    ----------------------------------------------------------------------
    -- Put × File: når put kommer først, står filoperationen i indeks inj i v,
    -- og præbetingelsen bygges med proj-inj: trans (proj-inj i v) p.
    -- For fopen og fclose ender de to sider i indeks, der kun er propositionelt
    -- ens (inj-comm), så fortsættelsen er et Tm (program for ethvert indeks).

    -- Put-Fopen
    eqPutFopen : (i : I) (v : a) (p : getOC i ≡ Closed) (f : String)
               → Equation Full Tm ⊥₁ i j₀
    eqPutFopen i v p f =
        (λ t → op (i₂ (i₁ (set inj v
                 (op (i₂ (i₂ (fopen getOC (trans (proj-inj i v) p) injₒ f
                                    (t (injₒ (inj i v) SOpen))))))))))
      ≐ (λ t → op (i₂ (i₂ (fopen getOC p injₒ f
                 (op (i₂ (i₁ (set inj v (t (inj (injₒ i SOpen) v))))))))))

    -- Put-Fread
    eqPutFread : (i : I) (v : a) (p : getOC i ≡ Open)
               → Equation Full (String → Ti (inj i v)) ⊥₁ i j₀
    eqPutFread i v p =
        (λ kr → op (i₂ (i₁ (set inj v
                  (op (i₂ (i₂ (fread getOC (trans (proj-inj i v) p) (λ r → kr r)))))))))
      ≐ (λ kr → op (i₂ (i₂ (fread getOC p (λ r →
                  op (i₂ (i₁ (set inj v (kr r)))))))))

    -- Put-Fwrite
    eqPutFwrite : (i : I) (v : a) (p : getOC i ≡ Open) (t : String)
                → Equation Full (Ti (inj i v)) ⊥₁ i j₀
    eqPutFwrite i v p t =
        (λ ku → op (i₂ (i₁ (set inj v
                  (op (i₂ (i₂ (fwrite getOC (trans (proj-inj i v) p) t ku))))))))
      ≐ (λ ku → op (i₂ (i₂ (fwrite getOC p t
                  (op (i₂ (i₁ (set inj v ku))))))))

    -- Put-Fclose
    eqPutFclose : (i : I) (v : a) (p : getOC i ≡ Open)
                → Equation Full Tm ⊥₁ i j₀
    eqPutFclose i v p =
        (λ t → op (i₂ (i₁ (set inj v
                 (op (i₂ (i₂ (fclose getOC (trans (proj-inj i v) p) injc
                                     (t (injc (inj i v) SClosed))))))))))
      ≐ (λ t → op (i₂ (i₂ (fclose getOC p injc
                 (op (i₂ (i₁ (set inj v (t (inj (injc i SClosed) v))))))))))

    ----------------------------------------------------------------------
    -- Typer på beviserne

    eqGetFopen-ok : ∀ i p f
      → respects {Σ = Full} {C = C} ⦃ fFull ⦄ algD (eqGetFopen i p f)
    -- højresiden læser i indeks injₒ i SOpen, så proj skal være uafhængig af injₒ
    eqGetFopen-ok i p f gen ka =
      funext (λ hd → cong (λ s → Fd gen (ka s) hd) (sym (ProjInjIndep.proj-inj pio i SOpen)))

    eqGetFread-ok : ∀ i p
      → respects {Σ = Full} {C = C} ⦃ fFull ⦄ algD (eqGetFread i p)
    eqGetFread-ok i p gen kb = refl

    eqGetFwrite-ok : ∀ i p t′
      → respects {Σ = Full} {C = C} ⦃ fFull ⦄ algD (eqGetFwrite i p t′)
    eqGetFwrite-ok i p t′ gen ka = refl

    eqGetFclose-ok : ∀ i p
      → respects {Σ = Full} {C = C} ⦃ fFull ⦄ algD (eqGetFclose i p)
    eqGetFclose-ok i p gen ka =
      funext (λ hd → cong (λ s → Fd gen (ka s) hd) (sym (ProjInjIndep.proj-inj pic i SClosed)))

    eqPutFopen-ok : ∀ i v p f
      → respects {Σ = Full} {C = C} ⦃ fFull ⦄ algD (eqPutFopen i v p f)
    eqPutFopen-ok i v p f gen t =
      funext (λ hd → cong (λ n → Fd gen (t n) hd) (inj-comm i SOpen v))

    eqPutFread-ok : ∀ i v p
      → respects {Σ = Full} {C = C} ⦃ fFull ⦄ algD (eqPutFread i v p)
    eqPutFread-ok i v p gen kr = refl

    eqPutFwrite-ok : ∀ i v p t′
      → respects {Σ = Full} {C = C} ⦃ fFull ⦄ algD (eqPutFwrite i v p t′)
    eqPutFwrite-ok i v p t′ gen ku = refl

    eqPutFclose-ok : ∀ i v p
      → respects {Σ = Full} {C = C} ⦃ fFull ⦄ algD (eqPutFclose i v p)
    eqPutFclose-ok i v p gen t =
      funext (λ hd → cong (λ n → Fd gen (t n) hd) (InjInjComm.inj-comm ic′ i SClosed v))


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
--   -- Kørsel

  genD : A → C j₀ j₀
  genD x = λ hd m → (just x , j₀) , m

  -- et throw uden handler giver nothing (sluttilstanden er fejlindekset s)
  runD : ∀ {i} → Free Full A i j₀ → D i j₀
  runD t = fold {C = C} ⦃ fFull ⦄ genD algD t (λ s m → (nothing , s) , m)