module Slopp.FileExample where

open import Data.Nat     using (ℕ; zero; suc; _+_)
open import Data.Maybe   using (just; nothing)
open import Data.Unit    using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Slopp.PHexc2
open import Slopp.StateSig
open import Slopp.FHAlg
open import Slopp.CombinedFile
open import Level using (suc; zero; lift)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import Slopp.PEquivComp

record ⊤₁ : Set₁ where
  constructor tt₁

I′ : Set
I′ = ℕ × FStatus

projSt : ProjL I′ ℕ
projSt = proj₁

injSt : InjL I′ ℕ I′
injSt (_ , fs) n = (n , fs)

getOC′ : ProjF I′
getOC′ = proj₂

injO : InjF I′ Open I′
injO (n , _) SOpen = (n , Open)

injC : InjF I′ Closed I′
injC (n , _) SClosed = (n , Closed)

pi : ProjInjIndep getOC′ injSt
pi = record { proj-inj = λ _ _ → refl }

icO : InjInjComm injO injSt
icO = record { inj-comm = λ { _ SOpen _ → refl } }

icC : InjInjComm injC injSt
icC = record { inj-comm = λ { _ SClosed _ → refl } }

open FileAlg I′ ⊤₁ (0 , Closed) (0 , Closed) (0 , Open) (0 , Open)

module StL = StateLaws projSt injSt
module FlL = FileLaws
module TnL = TensorLaws projSt injSt getOC′ injO injC pi icO icC

_>>==_ : ∀ {A B : Set₁} {i j k} → Free Full A i j → (A → Free Full B j k) → Free Full B i k
_>>==_ = _>>=_ ⦃ fFull ⦄

-- det der kommer efter catch (filen er lukket)
rest : ⊤₁ → Free Full ⊤₁ (0 , Closed) (0 , Closed)
rest _ =
  op (i₂ (i₂ (fopen getOC′ refl injO "ff"
    (op (i₂ (i₂ (fwrite getOC′ refl "hello"
      (op (i₂ (i₂ (fclose getOC′ refl injC (pure tt₁))))))))))))

-- handleren matcher på filstatus: i Open lukker den filen
handler : (s : I′) → Free Full ⊤₁ s (0 , Closed)
handler (n , Open)   =
  op (i₂ (i₁ (set injSt 0
    (op (i₂ (i₂ (fclose getOC′ refl injC (pure tt₁))))))))
handler (n , Closed) =
  op (i₂ (i₁ (set injSt 0 (pure tt₁))))

-- end j tt i kroppen
program2 : Free Full ⊤₁ (0 , Closed) (0 , Closed)
program2 =
  op (i₂ (i₂ (fopen getOC′ refl injO "f"
    (op (i₁ (catch {k = (0 , Open)} {A = ⊤}
       (λ j → op (i₂ (i₂ (fwrite getOC′ refl "GoodMorning" (op (i₁ (end j tt)))))))
       handler
       (λ _ → op (i₂ (i₂ (fclose getOC′ refl injC (pure tt₁)))))))
     >>== rest))))

-- throw i kroppen: handleren skal lukke filen i Open
program1 : Free Full ⊤₁ (0 , Closed) (0 , Closed)
program1 =
  op (i₂ (i₂ (fopen getOC′ refl injO "f"
    (op (i₁ (catch {k = (0 , Open)} {A = ⊤}
       (λ j → op (i₂ (i₁ (set injSt 42
                (op (i₂ (i₂ (fwrite getOC′ refl "GoodMorning" (op (i₁ throw))))))))))
       handler
       (λ _ → op (i₂ (i₂ (fclose getOC′ refl injC (pure tt₁)))))))
     >>== rest))))

test-good : runD program2 (0 , Closed) "init" ≡ ((just tt₁ , (0 , Closed)) , "hello")
test-good = refl

test-throw : runD program1 (0 , Closed) "init" ≡ ((just tt₁ , (0 , Closed)) , "hello")
test-throw = refl


------------------------------------------------------------------------
-- 1. Teorien T : Theory Full for State + File + Tensor

open-close-coh : ∀ i → getOC′ i ≡ Closed → injC (injO i SOpen) SClosed ≡ i
open-close-coh (_ , Closed) refl = refl

data FileTheory : Theory Full where
  -- State-love
  th-look-discard : ∀ {i} → FileTheory (liftΓ (StL.eqLookDiscard i))
  th-set-look     : ∀ {i s} → FileTheory (liftΓ (StL.eqSetLook i s))
  th-look-set     : ∀ {i} → FileTheory (StL.eqLookSet i)
  th-look-look    : ∀ {i} → FileTheory (liftΓ (StL.eqLookLook i))
  th-set-set      : ∀ {i s₁ s₂} → FileTheory (liftΓ (StL.eqSetSet i s₁ s₂ refl))

  -- Fil-love
  th-open-close   : ∀ {i pₒ p꜀} → FileTheory (liftΓ (FlL.eqOpenClose i getOC′ getOC′ pₒ injO p꜀ injC (open-close-coh i pₒ)))  
  th-write-write  : ∀ {i p} → FileTheory (liftΓ (FlL.eqWriteWrite i getOC′ p))
  th-write-read   : ∀ {i p} → FileTheory (liftΓ (FlL.eqWriteRead i getOC′ p))
  th-read-discard : ∀ {i p} → FileTheory (liftΓ (FlL.eqReadDiscard i getOC′ p))
  th-read-write   : ∀ {i p} → FileTheory (liftΓ (FlL.eqReadWrite i getOC′ p))
  th-read-read    : ∀ {i p} → FileTheory (liftΓ (FlL.eqReadRead i getOC′ p))

  -- Tensor-love
  th-get-fopen    : ∀ {i p f} → FileTheory (liftΓ (TnL.eqGetFopen i p f))
  th-get-fread    : ∀ {i p} → FileTheory (liftΓ (TnL.eqGetFread i p))
  th-get-fwrite   : ∀ {i p t} → FileTheory (liftΓ (TnL.eqGetFwrite i p t))
  th-get-fclose   : ∀ {i p} → FileTheory (liftΓ (TnL.eqGetFclose i p))
  th-put-fopen    : ∀ {i v p f} → FileTheory (liftΓ (TnL.eqPutFopen i v p f))
  th-put-fread    : ∀ {i v p} → FileTheory (liftΓ (TnL.eqPutFread i v p))
  th-put-fwrite   : ∀ {i v p t} → FileTheory (liftΓ (TnL.eqPutFwrite i v p t))
  th-put-fclose   : ∀ {i v p} → FileTheory (liftΓ (TnL.eqPutFclose i v p))

open EquivalentComputations ⦃ fFull ⦄ FileTheory

------------------------------------------------------------------------
-- 2. Eksempel på kongruensbevis med ~cong og ~eq:
--    Åbn fil → skriv "draft" → skriv "final" → luk fil
--    ~
--    Åbn fil → skriv "final" → luk fil

prog-double-write : Free Full ⊤₁ (0 , Closed) (0 , Closed)
prog-double-write =
  op (i₂ (i₂ (fopen getOC′ refl injO "log.txt"
    (op (i₂ (i₂ (fwrite getOC′ refl "draft"
      (op (i₂ (i₂ (fwrite getOC′ refl "final"
        (op (i₂ (i₂ (fclose getOC′ refl injC (pure tt₁))))))))))))))))

prog-single-write : Free Full ⊤₁ (0 , Closed) (0 , Closed)
prog-single-write =
  op (i₂ (i₂ (fopen getOC′ refl injO "log.txt"
    (op (i₂ (i₂ (fwrite getOC′ refl "final"
      (op (i₂ (i₂ (fclose getOC′ refl injC (pure tt₁))))))))))))

-- Fortsættelsen efter Write-Write: luk filen og returnér tt₁
k-close : FlL.FV → Free Full ⊤₁ (0 , Open) (0 , Closed)
k-close _ = op (i₂ (i₂ (fclose getOC′ refl injC (pure tt₁))))

-- Bevis via kongruens under fopen (~cong) + Write-Write foran k-close (~eq)
-- Helt uden {-# TERMINATING #-}:
equiv-writes : prog-double-write ~ prog-single-write
equiv-writes =
  ~cong (i₂ (i₂ (fopen getOC′ refl injO "log.txt" (pure tt₁))))
        (λ { (pure tt₁) → op (i₂ (i₂ (fwrite getOC′ refl "draft"
                            (op (i₂ (i₂ (fwrite getOC′ refl "final"
                              (op (i₂ (i₂ (fclose getOC′ refl injC (pure tt₁))))))))))))
           ; (op _)     → op (i₁ throw) })
        (λ { (pure tt₁) → op (i₂ (i₂ (fwrite getOC′ refl "final"
                            (op (i₂ (i₂ (fclose getOC′ refl injC (pure tt₁))))))))
           ; (op _)     → op (i₁ throw) })
        (λ { (pure tt₁) → ~eq th-write-write (lift ("draft" , "final")) k-close
           ; (op _)     → ~refl })




-- Program 1: åbn fil → skriv "draft" → sæt state til 7 → skriv "final" → luk fil
prog-state-between : Free Full ⊤₁ (0 , Closed) (7 , Closed)
prog-state-between =
  op (i₂ (i₂ (fopen getOC′ refl injO "log.txt"
    (op (i₂ (i₂ (fwrite getOC′ refl "draft"
      (op (i₂ (i₁ (set injSt 7
        (op (i₂ (i₂ (fwrite getOC′ refl "final"
          (op (i₂ (i₂ (fclose getOC′ refl injC (pure tt₁))))))))))))))))))))

-- Mellemtrin: byt set 7 og fwrite "final" via Put-Fwrite
prog-state-after : Free Full ⊤₁ (0 , Closed) (7 , Closed)
prog-state-after =
  op (i₂ (i₂ (fopen getOC′ refl injO "log.txt"
    (op (i₂ (i₂ (fwrite getOC′ refl "draft"
      (op (i₂ (i₂ (fwrite getOC′ refl "final"
        (op (i₂ (i₁ (set injSt 7
          (op (i₂ (i₂ (fclose getOC′ refl injC (pure tt₁))))))))))))))))))))

-- Slutprogram: kollaps de to skrivninger til én via Write-Write
prog-collapsed : Free Full ⊤₁ (0 , Closed) (7 , Closed)
prog-collapsed =
  op (i₂ (i₂ (fopen getOC′ refl injO "log.txt"
    (op (i₂ (i₂ (fwrite getOC′ refl "final"
      (op (i₂ (i₁ (set injSt 7
        (op (i₂ (i₂ (fclose getOC′ refl injC (pure tt₁))))))))))))))))

k-close-7 : TnL.TV → Free Full ⊤₁ (7 , Open) (7 , Closed)
k-close-7 _ = op (i₂ (i₂ (fclose getOC′ refl injC (pure tt₁))))

k-set-close-7 : FlL.FV → Free Full ⊤₁ (0 , Open) (7 , Closed)
k-set-close-7 _ =
  op (i₂ (i₁ (set injSt 7
    (op (i₂ (i₂ (fclose getOC′ refl injC (pure tt₁))))))))

-- Trin 1: Put-Fwrite under (fopen >> fwrite "draft")
step1 : prog-state-between ~ prog-state-after
step1 =
  ~cong (i₂ (i₂ (fopen getOC′ refl injO "log.txt" (pure tt₁))))
        (λ { (pure tt₁) → op (i₂ (i₂ (fwrite getOC′ refl "draft"
                            (op (i₂ (i₁ (set injSt 7
                              (op (i₂ (i₂ (fwrite getOC′ refl "final"
                                (op (i₂ (i₂ (fclose getOC′ refl injC (pure tt₁))))))))))))))))
           ; (op _)     → op (i₁ throw) })
        (λ { (pure tt₁) → op (i₂ (i₂ (fwrite getOC′ refl "draft"
                            (op (i₂ (i₂ (fwrite getOC′ refl "final"
                              (op (i₂ (i₁ (set injSt 7
                                (op (i₂ (i₂ (fclose getOC′ refl injC (pure tt₁))))))))))))))))
           ; (op _)     → op (i₁ throw) })
        (λ { (pure tt₁) →
               ~cong (i₂ (i₂ (fwrite getOC′ refl "draft" (pure tt₁))))
                     (λ { (pure tt₁) → op (i₂ (i₁ (set injSt 7
                                         (op (i₂ (i₂ (fwrite getOC′ refl "final"
                                           (op (i₂ (i₂ (fclose getOC′ refl injC (pure tt₁))))))))))))
                        ; (op _)     → op (i₁ throw) })
                     (λ { (pure tt₁) → op (i₂ (i₂ (fwrite getOC′ refl "final"
                                         (op (i₂ (i₁ (set injSt 7
                                           (op (i₂ (i₂ (fclose getOC′ refl injC (pure tt₁))))))))))))
                        ; (op _)     → op (i₁ throw) })
                     (λ { (pure tt₁) → ~eq th-put-fwrite (lift tt) k-close-7
                        ; (op _)     → ~refl })
           ; (op _) → ~refl })

-- Trin 2: Write-Write under fopen
step2 : prog-state-after ~ prog-collapsed
step2 =
  ~cong (i₂ (i₂ (fopen getOC′ refl injO "log.txt" (pure tt₁))))
        (λ { (pure tt₁) → op (i₂ (i₂ (fwrite getOC′ refl "draft"
                            (op (i₂ (i₂ (fwrite getOC′ refl "final"
                              (op (i₂ (i₁ (set injSt 7
                                (op (i₂ (i₂ (fclose getOC′ refl injC (pure tt₁))))))))))))))))
           ; (op _)     → op (i₁ throw) })
        (λ { (pure tt₁) → op (i₂ (i₂ (fwrite getOC′ refl "final"
                            (op (i₂ (i₁ (set injSt 7
                              (op (i₂ (i₂ (fclose getOC′ refl injC (pure tt₁))))))))))))
           ; (op _)     → op (i₁ throw) })
        (λ { (pure tt₁) → ~eq th-write-write (lift ("draft" , "final")) k-set-close-7
           ; (op _)     → ~refl })

equiv-tensor-optimize : prog-state-between ~ prog-collapsed
equiv-tensor-optimize = ~trans step1 step2