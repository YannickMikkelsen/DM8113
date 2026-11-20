module Slopp.CombinedTheory where
 
-- Tre teorier (state, fil, Exc), tensor-produktet StateAx ⊗ FileAx og den
-- kombinerede teori ExcAx ∪ (StateAx ⊗ FileAx) over Full. Alle aksiomer er ligninger fra CombinedFile
-- (kun Free). Sammenhængsbetingelserne (coh osv.) er felter i konstruktørerne:
-- loven er kun et aksiom for sammenhængende proj/inj-par.
-- IKKE typechecket.
 
open import Data.String  using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
 
open import Slopp.PHexc
open import Slopp.Lawful
open import Slopp.StateSig
open import Slopp.FHAlg
open import Slopp.PExcGen
open import Slopp.Theory
open import Slopp.CombinedFile
 
module CombinedTheory (I : Set) (A : Set₁) (i₀ j₀ k₀ m₀ : I) where
 
  open FileAlg I A i₀ j₀ k₀ m₀
 
  -- Exc-teorien fra Gen, instantieret med Sg og D, αD
  module E = ExcTheory Sg ⦃ fSg ⦄ lawfulSg i₀ j₀ k₀ m₀ D αD
 
  ----------------------------------------------------------------------
  -- State-teorien
 
  record SCtx : Set₁ where
    field
      a    : Set
      proj : ProjL I a
      inj  : InjL I a I
 
  module SL (c : SCtx) = StateLaws {SCtx.a c} (SCtx.proj c) (SCtx.inj c)
 
  data StateAx : ∀ {i j : I} {Γ Q : Set₁} → Equation Full Γ Q i j → Set₁ where
    ax-look-discard : ∀ (c : SCtx) (i : I) → StateAx (SL.eqLookDiscard c i)
    ax-set-look     : ∀ (c : SCtx) (i : I)
                    → (∀ st s → SCtx.proj c (SCtx.inj c st s) ≡ s)
                    → StateAx (SL.eqSetLook c i)
    ax-look-set     : ∀ (c : SCtx) (i : I)
                    → (SCtx.inj c i (SCtx.proj c i) ≡ i)
                    → StateAx (SL.eqLookSet c i)
    ax-look-look    : ∀ (c : SCtx) (i : I) → StateAx (SL.eqLookLook c i)
    ax-set-set      : ∀ (c : SCtx) (i : I)
                    → (∀ st s₁ s₂ → SCtx.inj c (SCtx.inj c st s₁) s₂ ≡ SCtx.inj c st s₂)
                    → StateAx (SL.eqSetSet c i)
 
  stateModel : Models {Σ = Full} ⦃ fFull ⦄ StateAx {C = C} {j₀ = j₀} algD
  stateModel _ (ax-look-discard c i)       = SL.eqLookDiscard-ok c i
  stateModel _ (ax-set-look c i coh)       = SL.eqSetLook-ok c i coh
  stateModel _ (ax-look-set c i coh-i)     = SL.eqLookSet-ok c i coh-i
  stateModel _ (ax-look-look c i)          = SL.eqLookLook-ok c i
  stateModel _ (ax-set-set c i coh)        = SL.eqSetSet-ok c i coh
 
  ----------------------------------------------------------------------
  -- Fil-teorien
 
  data FileAx : ∀ {i j : I} {Γ Q : Set₁} → Equation Full Γ Q i j → Set₁ where
    ax-open-close   : ∀ (i : I) (getOCₒ getOC꜀ : ProjF I)
                        (pₒ : getOCₒ i ≡ Closed) (injₒ : InjF I Open I)
                        (p꜀ : getOC꜀ (injₒ i SOpen) ≡ Open) (inj꜀ : InjF I Closed I)
                    → (inj꜀ (injₒ i SOpen) SClosed ≡ i)
                    → FileAx (FileLaws.eqOpenClose i getOCₒ getOC꜀ pₒ injₒ p꜀ inj꜀)
    ax-write-write  : ∀ (i : I) (getOC : ProjF I) (p : getOC i ≡ Open)
                    → FileAx (FileLaws.eqWriteWrite i getOC p)
    ax-write-read   : ∀ (i : I) (getOC : ProjF I) (p : getOC i ≡ Open)
                    → FileAx (FileLaws.eqWriteRead i getOC p)
    ax-read-discard : ∀ (i : I) (getOC : ProjF I) (p : getOC i ≡ Open)
                    → FileAx (FileLaws.eqReadDiscard i getOC p)
    ax-read-write   : ∀ (i : I) (getOC : ProjF I) (p : getOC i ≡ Open)
                    → FileAx (FileLaws.eqReadWrite i getOC p)
    ax-read-read    : ∀ (i : I) (getOC : ProjF I) (p : getOC i ≡ Open)
                    → FileAx (FileLaws.eqReadRead i getOC p)
 
  fileModel : Models {Σ = Full} ⦃ fFull ⦄ FileAx {C = C} {j₀ = j₀} algD
  fileModel _ (ax-open-close i gₒ g꜀ pₒ injₒ p꜀ inj꜀ coh) =
    FileLaws.eqOpenClose-ok i gₒ g꜀ pₒ injₒ p꜀ inj꜀ coh
  fileModel _ (ax-write-write i g p)  = FileLaws.eqWriteWrite-ok i g p
  fileModel _ (ax-write-read i g p)   = FileLaws.eqWriteRead-ok i g p
  fileModel _ (ax-read-discard i g p) = FileLaws.eqReadDiscard-ok i g p
  fileModel _ (ax-read-write i g p)   = FileLaws.eqReadWrite-ok i g p
  fileModel _ (ax-read-read i g p)    = FileLaws.eqReadRead-ok i g p
 
  ----------------------------------------------------------------------
  -- Kommutationslove mellem state- og fil-operationer.
  -- Det er IKKE en teori i sig selv: det er de love, som tensor-produktet
  -- StateAx ⊗ FileAx tilføjer (hver state-operation kommuterer med hver fil-operation).
 
  record TCtx : Set₁ where
    field
      a     : Set
      proj  : ProjL I a
      inj   : InjL I a I
      getOC : ProjF I
      injₒ  : InjF I Open I
      injc  : InjF I Closed I
      pi    : ProjInjIndep getOC inj
      ic    : InjInjComm injₒ inj
      ic′   : InjInjComm injc inj
      pio   : ProjInjIndep proj injₒ
      pic   : ProjInjIndep proj injc

  module TL (c : TCtx) =
    TensorLaws {TCtx.a c} (TCtx.proj c) (TCtx.inj c) (TCtx.getOC c)
               (TCtx.injₒ c) (TCtx.injc c) (TCtx.pi c) (TCtx.ic c) (TCtx.ic′ c)
               (TCtx.pio c) (TCtx.pic c)
 
  data CommSF : ∀ {i j : I} {Γ Q : Set₁} → Equation Full Γ Q i j → Set₁ where
    ax-get-fopen  : ∀ (c : TCtx) (i : I) (p : TCtx.getOC c i ≡ Closed) (f : String)
                  → CommSF (TL.eqGetFopen c i p f)
    ax-get-fread  : ∀ (c : TCtx) (i : I) (p : TCtx.getOC c i ≡ Open)
                  → CommSF (TL.eqGetFread c i p)
    ax-get-fwrite : ∀ (c : TCtx) (i : I) (p : TCtx.getOC c i ≡ Open) (t : String)
                  → CommSF (TL.eqGetFwrite c i p t)
    ax-get-fclose : ∀ (c : TCtx) (i : I) (p : TCtx.getOC c i ≡ Open)
                  → CommSF (TL.eqGetFclose c i p)
    ax-put-fopen  : ∀ (c : TCtx) (i : I) (v : TCtx.a c)
                      (p : TCtx.getOC c i ≡ Closed) (f : String)
                  → CommSF (TL.eqPutFopen c i v p f)
    ax-put-fread  : ∀ (c : TCtx) (i : I) (v : TCtx.a c) (p : TCtx.getOC c i ≡ Open)
                  → CommSF (TL.eqPutFread c i v p)
    ax-put-fwrite : ∀ (c : TCtx) (i : I) (v : TCtx.a c) (p : TCtx.getOC c i ≡ Open)
                      (t : String)
                  → CommSF (TL.eqPutFwrite c i v p t)
    ax-put-fclose : ∀ (c : TCtx) (i : I) (v : TCtx.a c) (p : TCtx.getOC c i ≡ Open)
                  → CommSF (TL.eqPutFclose c i v p)
 
  commSFModel : Models {Σ = Full} ⦃ fFull ⦄ CommSF {C = C} {j₀ = j₀} algD
  commSFModel _ (ax-get-fopen c i p f)    = TL.eqGetFopen-ok c i p f
  commSFModel _ (ax-get-fread c i p)      = TL.eqGetFread-ok c i p
  commSFModel _ (ax-get-fwrite c i p t)   = TL.eqGetFwrite-ok c i p t
  commSFModel _ (ax-get-fclose c i p)     = TL.eqGetFclose-ok c i p
  commSFModel _ (ax-put-fopen c i v p f)  = TL.eqPutFopen-ok c i v p f
  commSFModel _ (ax-put-fread c i v p)    = TL.eqPutFread-ok c i v p
  commSFModel _ (ax-put-fwrite c i v p t) = TL.eqPutFwrite-ok c i v p t
  commSFModel _ (ax-put-fclose c i v p)   = TL.eqPutFclose-ok c i v p
 
  ----------------------------------------------------------------------
  -- Tensor af state og fil: StateAx ⊗ FileAx (med kommutationslovene CommSF)
 
  StateFile : Theory Full
  StateFile = StateAx ⊗⟨ CommSF ⟩ FileAx
 
  stateFileModel : Models {Σ = Full} ⦃ fFull ⦄ StateFile {C = C} {j₀ = j₀} algD
  stateFileModel = ⊗-model ⦃ fFull ⦄ stateModel fileModel commSFModel
 
  ----------------------------------------------------------------------
  -- Den kombinerede teori: Exc lagt ovenpå tensor-produktet af state og fil
 
  CombAx : Theory Full
  CombAx = E.ExcAx ∪ StateFile
 
  combModel : Models {Σ = Full} ⦃ fFull ⦄ CombAx {C = C} {j₀ = j₀} algD
  combModel = ∪-model ⦃ fFull ⦄ E.excModel stateFileModel