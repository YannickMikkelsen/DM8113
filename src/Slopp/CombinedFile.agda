{-# OPTIONS --allow-unsolved-metas #-}
module Slopp.CombinedFile where

-- Parameterized udgave: state + fil kombineres, og Gen (Exc-delen) lægges
-- ovenpå. IKKE typechecket. Lovene bevises bagefter.

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
  D i j = I → HF {I} R i j

  αD : ∀ {a} → Sg D a j₀ → D a j₀
  αD (i₁ (look proj k))   = λ s → k (proj s) s
  αD (i₁ (set inj val k)) = λ s → k (inj s val)
  αD (i₂ f)               = λ s → algFile (fmap ⦃ fFile ⦄ {X = D} {Y = HF {I} R} {j = j₀} {j' = j₀}
                                               (λ {i} k → k s) f)

  module G = Gen Sg ⦃ fSg ⦄ lawfulSg i₀ j₀ k₀ m₀ D αD

  Full : (I → I → Set₁) → (I → I → Set₁)
  Full = G.S              -- = Exc J + (StateOp + FileOpS)

  fFull : Functor Full
  fFull = Functor+ ⦃ fExc ⦄ ⦃ fSg ⦄

  C : I → I → Set₁
  C = G.C

  algD : ∀ {a} → Full C a j₀ → C a j₀
  algD = G.algE


  ----------------------------------------------------------------------
  -- State-love. Variablerne må sidde i ethvert indeks x (tv : ∀ {x} → ...),
  -- så vi slipper for at transportere ρ mellem indeks.

  module StateLaws {a : Set} (proj : ProjL I a) (inj : InjL I a I) where

    data SV : I → I → Set₁ where
      tv  : ∀ {x} → SV x j₀
      kv  : ∀ {x} → a → SV x j₀
      kv2 : ∀ {x} → a → a → SV x j₀

    -- Look-Discard: look proj (λ _ → tv) ≡ tv
    eqLookDiscard : (i : I) → Equation Full ⊤ SV i j₀
    eqLookDiscard i =
      (λ _ → opT (i₂ (i₁ (look proj (λ _ → var tv)))))
      ≐ (λ _ → var tv)

    -- Set-Look: set inj s (look proj (λ s' → kv s')) ≡ set inj s (kv s)
    --   side condition: proj (inj i s) ≡ s
    eqSetLook : (i : I) → Equation Full a SV i j₀
    eqSetLook i =
      (λ s → opT (i₂ (i₁ (set inj s (opT (i₂ (i₁ (look proj (λ s' → var (kv s'))))))))))
      ≐ (λ s → opT (i₂ (i₁ (set inj s (var (kv s))))))

    -- Look-Set: look proj (λ s → set inj s tv) ≡ tv
    --   side condition: inj i (proj i) ≡ i
    eqLookSet : (i : I) → Equation Full ⊤ SV i j₀
    eqLookSet i =
      (λ _ → opT (i₂ (i₁ (look proj (λ s → opT (i₂ (i₁ (set inj s (var tv)))))))))
      ≐ (λ _ → var tv) --ikke det samme som før nor vi nu gemmer informasion i staten

    -- Look-Look: look proj (λ s → look proj (λ s' → kv2 s s')) ≡ look proj (λ s → kv2 s s)
    eqLookLook : (i : I) → Equation Full ⊤ SV i j₀
    eqLookLook i =
      (λ _ → opT (i₂ (i₁ (look proj (λ s →
                opT (i₂ (i₁ (look proj (λ s' → var (kv2 s s'))))))))))
      ≐ (λ _ → opT (i₂ (i₁ (look proj (λ s → var (kv2 s s))))))

    -- Set-Set: set inj s₁ (set inj s₂ tv) ≡ set inj s₂ tv
    --   side condition: inj (inj i s₁) s₂ ≡ inj i s₂
    eqSetSet : (i : I) → Equation Full (a × a) SV i j₀
    eqSetSet i =
      (λ { (s₁ , s₂) → opT (i₂ (i₁ (set inj s₁ (opT (i₂ (i₁ (set inj s₂ (var tv))))))))})
      ≐ (λ { (_ , s₂) → opT (i₂ (i₁ (set inj s₂ (var tv)))) })

    ----------------------------------------------------------------------
    -- Typer på beviserne. Side conditions tages for alle køretidstilstande st,
    -- fordi D bruger I som tilstand.

    eqLookDiscard-ok : ∀ i
      → respects {Σ = Full} {C = C} ⦃ fFull ⦄ algD (eqLookDiscard i)
    eqLookDiscard-ok i ρ t = refl

    eqSetLook-ok : ∀ i
      → (∀ st s → proj (inj st s) ≡ s)
      → respects {Σ = Full} {C = C} ⦃ fFull ⦄ algD (eqSetLook i)
    eqSetLook-ok i coh ρ t = funext (λ hb → funext (λ s → cong (λ x → ρ (kv x) hb (inj s t)) (coh s t)))

    eqLookSet-ok : ∀ i
      → (∀ st → inj st (proj st) ≡ st)
      → respects {Σ = Full} {C = C} ⦃ fFull ⦄ algD (eqLookSet i)
    eqLookSet-ok i coh ρ t = {!   !} -- kan ikke løses skal enuraers

    eqLookLook-ok : ∀ i
      → respects {Σ = Full} {C = C} ⦃ fFull ⦄ algD (eqLookLook i)
    eqLookLook-ok i ρ t = refl

    eqSetSet-ok : ∀ i
      → (∀ st s₁ s₂ → inj (inj st s₁) s₂ ≡ inj st s₂)
      → respects {Σ = Full} {C = C} ⦃ fFull ⦄ algD (eqSetSet i)
    eqSetSet-ok i coh ρ (s₁ , s₂) =
      funext (λ hd → funext (λ s →
        trans
          (cong (λ n → ρ {n} tv hd (inj (inj s s₁) s₂)) (coh i s₁ s₂))
          (cong (ρ {inj i s₂} tv hd) (coh s s₁ s₂))))
  ----------------------------------------------------------------------

  ----------------------------------------------------------------------
  -- Fil-love. Operationerne ligger i i₂ (i₂ ...) af Full.
  -- Variablerne må sidde i ethvert indeks x, som i StateLaws.
  -- Premisserne p : getOC i ≡ Open osv. tages som argumenter til ligningen,
  -- fordi de indgår i typen af fread/fwrite/fopen/fclose.

  module FileLaws where

    data FV : I → I → Set₁ where
      tt′ : ∀ {x} → FV x j₀
      kr  : ∀ {x} → String → FV x j₀
      kr2 : ∀ {x} → String → String → FV x j₀

    -- Open-Close: fopen getOCₒ pₒ injₒ f (fclose getOC꜀ p꜀ inj꜀ tt) ≡ tt
    --   side condition: inj꜀ (injₒ i SOpen) SClosed ≡ i
    eqOpenClose : (i : I)
                  (getOCₒ getOC꜀ : ProjF I)
                  (pₒ : getOCₒ i ≡ Closed)
                  (injₒ : InjF I Open I)
                  (p꜀ : getOC꜀ (injₒ i SOpen) ≡ Open)
                  (inj꜀ : InjF I Closed I)
                → Equation Full String FV i j₀
    eqOpenClose i getOCₒ getOC꜀ pₒ injₒ p꜀ inj꜀ =
      (λ f → opT (i₂ (i₂ (fopen getOCₒ pₒ injₒ f
                (opT (i₂ (i₂ (fclose getOC꜀ p꜀ inj꜀ (var tt′)))))))))
      ≐ (λ _ → var tt′)

    -- Write-Write: fwrite s₁ (fwrite s₂ tt) ≡ fwrite s₂ tt
    eqWriteWrite : (i : I) (getOC : ProjF I) (p : getOC i ≡ Open)
                 → Equation Full (String × String) FV i j₀
    eqWriteWrite i getOC p =
      (λ { (s₁ , s₂) → opT (i₂ (i₂ (fwrite getOC p s₁
                (opT (i₂ (i₂ (fwrite getOC p s₂ (var tt′)))))))) })
      ≐ (λ { (_ , s₂) → opT (i₂ (i₂ (fwrite getOC p s₂ (var tt′)))) })

    -- Write-Read: fwrite s (fread (λ r → kr r)) ≡ fwrite s (kr s)
    eqWriteRead : (i : I) (getOC : ProjF I) (p : getOC i ≡ Open)
                → Equation Full String FV i j₀
    eqWriteRead i getOC p =
      (λ s → opT (i₂ (i₂ (fwrite getOC p s
                (opT (i₂ (i₂ (fread getOC p (λ r → var (kr r))))))))))
      ≐ (λ s → opT (i₂ (i₂ (fwrite getOC p s (var (kr s))))))

    -- Read-Discard: fread (λ _ → tt) ≡ tt
    eqReadDiscard : (i : I) (getOC : ProjF I) (p : getOC i ≡ Open)
                  → Equation Full ⊤ FV i j₀
    eqReadDiscard i getOC p =
      (λ _ → opT (i₂ (i₂ (fread getOC p (λ _ → var tt′)))))
      ≐ (λ _ → var tt′)

    -- Read-Write: fread (λ s → fwrite s tt) ≡ tt
    eqReadWrite : (i : I) (getOC : ProjF I) (p : getOC i ≡ Open)
                → Equation Full ⊤ FV i j₀
    eqReadWrite i getOC p =
      (λ _ → opT (i₂ (i₂ (fread getOC p (λ s →
                opT (i₂ (i₂ (fwrite getOC p s (var tt′)))))))))
      ≐ (λ _ → var tt′)

    -- Read-Read: fread (λ s → fread (λ s' → kr2 s s')) ≡ fread (λ s → kr2 s s)
    eqReadRead : (i : I) (getOC : ProjF I) (p : getOC i ≡ Open)
               → Equation Full ⊤ FV i j₀
    eqReadRead i getOC p =
      (λ _ → opT (i₂ (i₂ (fread getOC p (λ s →
                opT (i₂ (i₂ (fread getOC p (λ s' → var (kr2 s s'))))))))))
      ≐ (λ _ → opT (i₂ (i₂ (fread getOC p (λ s → var (kr2 s s))))))

    ----------------------------------------------------------------------
    -- Typer på beviserne

    eqOpenClose-ok : ∀ i getOCₒ getOC꜀ pₒ injₒ p꜀ inj꜀
      → (inj꜀ (injₒ i SOpen) SClosed ≡ i)
      → respects {Σ = Full} {C = C} ⦃ fFull ⦄ algD
                 (eqOpenClose i getOCₒ getOC꜀ pₒ injₒ p꜀ inj꜀)
    eqOpenClose-ok i getOCₒ getOC꜀ pₒ injₒ p꜀ inj꜀ coh ρ t = funext (λ hb → cong (λ n → ρ {n} tt′ hb) coh)

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

  module TensorLaws {a : Set} (proj : ProjL I a) (inj : InjL I a I)
                    (getOC : ProjF I) (injₒ : InjF I Open I) (injc : InjF I Closed I)
                    (pi : ProjInjIndep getOC inj) (ic : InjInjComm injₒ inj) (ic′ : InjInjComm injc inj) where

    open ProjInjIndep pi
    open InjInjComm ic

    -- Variablerne sidder i ethvert indeks x, så de to sider må gerne ende i
    -- forskellige (kun propositionelt ens) indeks. Inj-Inj-Comm er
    -- papirbegrundelsen for, at de er ens.
    data TV : I → I → Set₁ where
      ka : ∀ {x} → a → TV x j₀               -- resultat fra look
      kb : ∀ {x} → a → String → TV x j₀      -- look og fread
      kr : ∀ {x} → String → TV x j₀          -- resultat fra fread
      ku : ∀ {x} → TV x j₀                   -- resultat fra en ⊤-operation

    ----------------------------------------------------------------------
    -- Get × File: look ændrer ikke indekset, så præbetingelsen p bruges direkte.

    -- Get-Fopen
    eqGetFopen : (i : I) (p : getOC i ≡ Closed) (f : String)
               → Equation Full ⊤ TV i j₀
    eqGetFopen i p f =
      (λ _ → opT (i₂ (i₁ (look proj (λ s →
               opT (i₂ (i₂ (fopen getOC p injₒ f (var (ka s))))))))))
      ≐ (λ _ → opT (i₂ (i₂ (fopen getOC p injₒ f
               (opT (i₂ (i₁ (look proj (λ s → var (ka s))))))))))

    -- Get-Fread
    eqGetFread : (i : I) (p : getOC i ≡ Open)
               → Equation Full ⊤ TV i j₀
    eqGetFread i p =
      (λ _ → opT (i₂ (i₁ (look proj (λ s →
               opT (i₂ (i₂ (fread getOC p (λ r → var (kb s r))))))))))
      ≐ (λ _ → opT (i₂ (i₂ (fread getOC p (λ r →
               opT (i₂ (i₁ (look proj (λ s → var (kb s r))))))))))

    -- Get-Fwrite
    eqGetFwrite : (i : I) (p : getOC i ≡ Open) (t : String)
                → Equation Full ⊤ TV i j₀
    eqGetFwrite i p t =
      (λ _ → opT (i₂ (i₁ (look proj (λ s →
               opT (i₂ (i₂ (fwrite getOC p t (var (ka s))))))))))
      ≐ (λ _ → opT (i₂ (i₂ (fwrite getOC p t
               (opT (i₂ (i₁ (look proj (λ s → var (ka s))))))))))

    -- Get-Fclose
    eqGetFclose : (i : I) (p : getOC i ≡ Open)
                → Equation Full ⊤ TV i j₀
    eqGetFclose i p =
      (λ _ → opT (i₂ (i₁ (look proj (λ s →
               opT (i₂ (i₂ (fclose getOC p injc (var (ka s))))))))))
      ≐ (λ _ → opT (i₂ (i₂ (fclose getOC p injc
               (opT (i₂ (i₁ (look proj (λ s → var (ka s))))))))))

    ----------------------------------------------------------------------
    -- Put × File: når put kommer først, står filoperationen i indeks inj i v,
    -- og præbetingelsen bygges med proj-inj: trans (proj-inj i v) p.

    -- Put-Fopen
    eqPutFopen : (i : I) (v : a) (p : getOC i ≡ Closed) (f : String)
               → Equation Full ⊤ TV i j₀
    eqPutFopen i v p f =
      (λ _ → opT (i₂ (i₁ (set inj v
               (opT (i₂ (i₂ (fopen getOC (trans (proj-inj i v) p) injₒ f (var ku)))))))))
      ≐ (λ _ → opT (i₂ (i₂ (fopen getOC p injₒ f
               (opT (i₂ (i₁ (set inj v (var ku)))))))))

    -- Put-Fread
    eqPutFread : (i : I) (v : a) (p : getOC i ≡ Open)
               → Equation Full ⊤ TV i j₀
    eqPutFread i v p =
      (λ _ → opT (i₂ (i₁ (set inj v
               (opT (i₂ (i₂ (fread getOC (trans (proj-inj i v) p) (λ r → var (kr r))))))))))
      ≐ (λ _ → opT (i₂ (i₂ (fread getOC p (λ r →
               opT (i₂ (i₁ (set inj v (var (kr r))))))))))

    -- Put-Fwrite
    eqPutFwrite : (i : I) (v : a) (p : getOC i ≡ Open) (t : String)
                → Equation Full ⊤ TV i j₀
    eqPutFwrite i v p t =
      (λ _ → opT (i₂ (i₁ (set inj v
               (opT (i₂ (i₂ (fwrite getOC (trans (proj-inj i v) p) t (var ku)))))))))
      ≐ (λ _ → opT (i₂ (i₂ (fwrite getOC p t
               (opT (i₂ (i₁ (set inj v (var ku)))))))))

    -- Put-Fclose
    eqPutFclose : (i : I) (v : a) (p : getOC i ≡ Open)
                → Equation Full ⊤ TV i j₀
    eqPutFclose i v p =
      (λ _ → opT (i₂ (i₁ (set inj v
               (opT (i₂ (i₂ (fclose getOC (trans (proj-inj i v) p) injc (var ku)))))))))
      ≐ (λ _ → opT (i₂ (i₂ (fclose getOC p injc
               (opT (i₂ (i₁ (set inj v (var ku)))))))))

    ----------------------------------------------------------------------
    -- Typer på beviserne

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
    eqPutFopen-ok i v p f ρ t = funext (λ hd → cong (λ n → λ s m → ρ {n} ku hd (inj s v) m) (inj-comm i SOpen v))

    eqPutFread-ok : ∀ i v p
      → respects {Σ = Full} {C = C} ⦃ fFull ⦄ algD (eqPutFread i v p)
    eqPutFread-ok i v p ρ t = refl

    eqPutFwrite-ok : ∀ i v p t′
      → respects {Σ = Full} {C = C} ⦃ fFull ⦄ algD (eqPutFwrite i v p t′)
    eqPutFwrite-ok i v p t′ ρ t = refl

    eqPutFclose-ok : ∀ i v p
      → respects {Σ = Full} {C = C} ⦃ fFull ⦄ algD (eqPutFclose i v p)
    eqPutFclose-ok i v p ρ t = funext (λ hd → cong (λ n → λ s m → ρ {n} ku hd (inj s v) m) (InjInjComm.inj-comm ic′ i SClosed v))


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
  genD x = λ hd s m → (just x , s) , m

  -- et throw uden handler giver nothing
  runD : ∀ {i} → Free Full A i j₀ → D i j₀
  runD t = fold {C = C} ⦃ fFull ⦄ genD algD t (λ s s' m → (nothing , s') , m)
