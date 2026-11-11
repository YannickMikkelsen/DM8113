module Slopp.FileExample where

open import Data.Maybe using (just; nothing)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Slopp.PHexc
open import Slopp.FHAlg
open import Slopp.CombinedFile

record ⊤₁ : Set₁ where
  constructor tt₁

I′ : Set
I′ = FStatus

getOC′ : ProjF I′
getOC′ s = s

injO : InjF I′ Open I′
injO _ SOpen = Open

injC : InjF I′ Closed I′
injC _ SClosed = Closed

open FileAlg I′ ⊤₁ Closed Closed Open Open

_>>==_ : ∀ {A B : Set₁} {i j} → Free Full A i j → (A → Free Full B j j) → Free Full B i j
_>>==_ = _>>=_ ⦃ fFull ⦄

-- det der kommer efter catch (filen er lukket)
rest : ⊤₁ → Free Full ⊤₁ Closed Closed
rest _ =
  op (i₂ (i₂ (fopen getOC′ refl injO "ff"
    (op (i₂ (i₂ (fwrite getOC′ refl "hello"
      (op (i₂ (i₂ (fclose getOC′ refl injC (pure tt₁))))))))))))

-- handleren matcher på tilstanden: i Open lukker den filen
handler : (s : I′) → Free Full ⊤₁ s Closed
handler Open   = op (i₂ (i₂ (fclose getOC′ refl injC (pure tt₁))))
handler Closed = pure tt₁

-- end j tt i kroppen
program2 : Free Full ⊤₁ Closed Closed
program2 =
  op (i₂ (i₂ (fopen getOC′ refl injO "f"
    (op (i₁ (catch {k = Open} {A = ⊤}
       (λ j → op (i₂ (i₂ (fwrite getOC′ refl "GoodMorning" (op (i₁ (end j tt)))))))
       (handler)
       (λ _ → op (i₂ (i₂ (fclose getOC′ refl injC (pure tt₁)))))))
     >>== rest))))

-- throw i kroppen: handleren skal lukke filen i Open
program1 : Free Full ⊤₁ Closed Closed
program1 =
  op (i₂ (i₂ (fopen getOC′ refl injO "f"
    (op (i₁ (catch {k = Open} {A = ⊤}
       (λ j → op (i₂ (i₂ (fwrite getOC′ refl "GoodMorning" (op (i₁ throw))))))
       handler
       (λ _ → op (i₂ (i₂ (fclose (getOC′) refl injC (pure tt₁)))))))
     >>== rest))))

-- Den lækkende handler kan IKKE skrives:
--   (λ s → pure tt₁)                       kræver s ≡ Closed for alle s
--   (λ s → op (… fopen getOC′ {!!} …))     kræver getOC′ s ≡ Closed for alle s

test-good : runD program2 Closed "init" ≡ ((just tt₁ , Closed) , "hello")
test-good = refl