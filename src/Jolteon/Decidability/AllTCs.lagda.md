<!--
```agda
{-# OPTIONS --safe #-}
open import Prelude
open import Hash

open import Jolteon.Assumptions

module Jolteon.Decidability.AllTCs (⋯ : _) (open Assumptions ⋯) where

open import Jolteon ⋯
open import Jolteon.Decidability.Core ⋯
open import Jolteon.Decidability.VoteSharesOf ⋯
```
-->

# The `allTCs` function and its properties

##

The function allTCs extracts all TCs in a list of messages.

```agda

record TimeoutEvidenceOf (r : Round) (ms : Messages) (ts : List TimeoutEvidence) : Type where
  field
    sound : ∀ {te} →
      te ∈ ts
      ─────────────────────────────────
      ∃ λ mtc → Timeout (te , mtc) ∈ ms
    complete : ∀ {te} → ⦃ te ∙round ≡ r ⦄ → ⦃ te< : te ∙qcTE ∙round < r ⦄ →
      Timeout (te , mtc) ∈ ms
      ────────────────────────
      te ∈ ts
    round≡ : All ((_≡ r) ∘ _∙round) ts
    qc<    : All (λ te → te ∙qcTE ∙round < r) ts

open TimeoutEvidenceOf
open L.All using (lookup) renaming (map to amap)
open L.Any using (tail)

timeoutEvidence⁺ : (r : Round) (ms : Messages) → ∃ (TimeoutEvidenceOf r ms)
timeoutEvidence⁺ r [] = [] , record
  { sound    = λ ()
  ; complete = λ ()
  ; round≡   = []
  ; qc<      = []
  }
timeoutEvidence⁺ r  ms₀@(m ∷ ms)
  with ts , rte ← timeoutEvidence⁺ r ms
  with ts⁺ ← (¬Timeout m → ∃ (TimeoutEvidenceOf r ms₀)) ∋ (λ m≢ →
    ts , record
    { sound    = map₂ there ∘ rte .sound
    ; complete = λ where (here refl) → ⊥-elim m≢; (there m∈) → rte .complete m∈
    ; round≡   = rte .round≡
    ; qc<      = rte .qc<
    })
  with m
... | Propose  _ = ts⁺ tt
... | TCFormed _ = ts⁺ tt
... | Vote _     = ts⁺ tt
... | Timeout (te , mtc)
  with (te ∙round) ≟ r | ¿ te ∙qcTE ∙round < r ¿
... | no te≢ | _    = ts , record
  { sound    = map₂ there ∘ rte .sound
  ; complete = λ where (here refl) → ⊥-elim (te≢ it) ; (there m∈) → rte .complete m∈
  ; round≡   = rte .round≡
  ; qc<      = rte .qc<
  }
... | yes _ | no qc≮ = ts , record
  { sound    = map₂ there ∘ rte .sound
  ; complete = λ where (here refl) → ⊥-elim (qc≮ it) ; (there m∈) → rte .complete m∈
  ; round≡   = rte .round≡
  ; qc<      = rte .qc<
  }
... | yes refl | yes qc<r = te ∷ ts , record
  { sound    = λ where
    (here refl) → mtc , here refl
    (there te∈) → map₂ there $ rte .sound te∈
  ; complete = λ where (here refl) → here it ; (there m∈) → there (rte .complete m∈)
  ; round≡   = refl ∷ rte .round≡
  ; qc<      = qc<r ∷ rte .qc<
  }

module _ r ms (let ts , p = timeoutEvidence⁺ r ms) where
  timeoutEvidence : List TimeoutEvidence
  timeoutEvidence = ts

  open TimeoutEvidenceOf p public renaming
    ( sound    to timeoutEvidence-sound
    ; complete to timeoutEvidence-complete
    ; round≡   to timeoutEvidence-≡
    ; qc<      to timeoutEvidence-qc<
    )

timeoutEvidence-maximal : ∀ tc ms →
  FormedTC tc ms
  ──────────────────────────────────────────
  tc .tes ⊆ˢ timeoutEvidence (tc ∙round) ms
timeoutEvidence-maximal tc ms ftc {te} te∈ with (te ∙round) ≟ (tc ∙round)
... | no ¬eq = ⊥-elim $ ¬eq $ lookup (getAllRound tc) te∈
... | yes refl with ¿ te ∙qcTE ∙round < (tc ∙round) ¿
... | no qc≮ =  ⊥-elim $ qc≮ $ lookup (getQCBound tc) te∈
... | yes teqc< = QED
  where

  m∈ : ∃ λ mtc → Timeout (te , mtc) ∈ ms
  m∈ = lookup ftc te∈

  QED : te ∈ timeoutEvidence (tc ∙round) ms
  QED = timeoutEvidence-complete (te ∙round) ms ⦃ te< = teqc< ⦄ (proj₂ m∈)

-- Decide if it is possible to construct a FormedTC in ms for round r.
Dec-∃FormedTC : ∀ r ms → Dec (∃ λ tc → (tc .roundTC ≡ r) × FormedTC tc ms)
Dec-∃FormedTC r ms with ¿ UniqueByMajority⊆ˢ node (timeoutEvidence r ms) ¿
... | no ¬ums
    = no λ where
     (tc , refl , ftc) →
       ¬ums $ tc .tes
            , timeoutEvidence-maximal tc ms ftc
            , getUniqueTC tc
            , getQuorumTC tc
... | yes (ps , ps⊆ , uniq , maj)
    = yes (mytc , refl , fmytc)
  where

  open ≡-Reasoning
  open L.All using (tabulate; map⁻; map⁺; lookup)
  open L.SubS using (All-resp-⊇)

  mytc : TC
  mytc =
    record
    { roundTC  = r
    ; tes      = ps
    ; quorumTC = maj
    ; uniqueTC = uniq
    ; allRound = All-resp-⊇ ps⊆ $ timeoutEvidence-≡  r ms
    ; qcBound  = All-resp-⊇ ps⊆ $ timeoutEvidence-qc< r ms
    }

  fmytc : FormedTC mytc ms
  fmytc = tabulate $ timeoutEvidence-sound r ms ∘ ps⊆

-- Decide if it is possible to construct a FormedTC with the given round from a
-- list of messages.
tryTC : ∀ r ms →
  ───────────────────────────────────────────────
  Dec $ ∃ λ tc → (tc ∙round ≡ r) × FormedTC tc ms
tryTC = Dec-∃FormedTC

record AllTCsOf (ms : Messages) (tcs : TCs) : Type where
  field
    sound    : tc ∈ tcs → tc ∙∈ ms
    complete : tc ∙∈ ms → tc .roundTC ∈ map roundTC tcs

open AllTCsOf
open L.All using () renaming (map to amap; zipWith to azipWith)
open L.Any using (tail; ++⁺ˡ)
open L.Mem using (∈-map⁺; ∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)

allTCs⁺ : (ms : Messages) → ∃ (AllTCsOf ms)
allTCs⁺ [] = [] , record
  { sound    = λ ()
  ; complete = λ where {tc} (formedTC x) →  ⊥-elim $ ¬FormedTC tc x
  }
  where
  ¬FormedTC : ∀ tc → ¬ FormedTC tc []
  ¬FormedTC tc ftc with tc .tes in tes≡ | ftc
  ... | [] | _ =  ⊥-elim $ majority⁺ (subst IsMajority tes≡ $ getQuorumTC tc)
  ... | _ ∷ _ | () ∷ _
allTCs⁺ (m ∷ ms)
  with ts , r ← allTCs⁺ ms
  with m
... | Propose (⟨ _ , nothing , _ , _ ⟩ signed-by _) =  ts , record
    { sound = λ tc∈ → tc∈-monotonic $ r .sound tc∈
    ; complete = λ where
      {tc} (formedTC p) → r .complete {tc} $
        formedTC $ amap (λ where (mtc , there tc∈) → mtc , tc∈) p
      (receivedTC (here (tc∈-Propose ())))
      (receivedTC (there p)) → r .complete (receivedTC p)
    }
... | Propose (⟨ bid , just tc , rb , txs ⟩ signed-by _) =  tc ∷ ts , record
    { sound =  λ where
      (here refl) → receivedTC $ here $′ tc∈-Propose refl
      (there tc∈) → tc∈-monotonic $ r .sound tc∈
    ; complete = λ where
      {tc} (formedTC p) → there $ r .complete {tc} $
        formedTC $ amap (λ where (mtc , there tm∈) → mtc , tm∈) p
      (receivedTC (here (tc∈-Propose refl))) → here refl
      (receivedTC (there p)) → there $ r .complete $ receivedTC p
    }
... | Vote v = ts , record
    { sound =  λ tc∈ → tc∈-monotonic $ r .sound tc∈
    ; complete = λ where
      {tc} (formedTC p) → r .complete $ formedTC {tc} $ amap (λ where (mtc , there tm∈) → mtc , tm∈) p
      (receivedTC p) → r .complete $ receivedTC $ tail (λ ()) p
    }
... | TCFormed tc =  tc ∷ ts , record
    { sound = λ where
      (here refl) → receivedTC $ here tc∈-TCFormed
      (there p) →  tc∈-monotonic $ r .sound p
    ; complete = λ where
     {tc} (formedTC p) → there $ r .complete {tc} $
       formedTC (amap (λ where (mtc , there tm∈) → mtc , tm∈) p)
     (receivedTC (here tc∈-TCFormed)) → here refl
     (receivedTC (there p)) → there $ r .complete $ receivedTC p
    }
... | Timeout (te , mtc)
  with tryTC (te ∙round) (Timeout (te , mtc) ∷ ms) | mtc in mtc≡
... | no ¬tc  | nothing = ts , record
      { sound = λ where tc∈ → tc∈-monotonic $ r .sound tc∈
      ; complete = λ where
        {tc} (formedTC p) → case (tc ∙round) ≟ (te ∙round) of λ
          where
          (yes eq) → ⊥-elim $ ¬tc (tc , eq ,
            amap (map₂ (subst (λ ◆ → Any _ (Timeout (te , ◆) ∷ ms)) (sym mtc≡))) p)
          (no ¬eq) → r .complete $ formedTC {tc} $
            azipWith (λ where ((mtc , te∈) , refl) → mtc , tail (λ where refl → ¬eq refl) te∈ )
                     (p , getAllRound tc)
        (receivedTC p) → r .complete $ receivedTC $ tail (λ where (tc∈-Timeout ())) p
      }
... | no ¬tc | (just tc) = tc ∷ ts , record
      { sound =  λ where
        (here refl) → receivedTC (here (tc∈-Timeout refl))
        (there p) → tc∈-monotonic (r .sound p)
      ; complete = λ where
        {tc′} (formedTC p) → case (tc′ ∙round) ≟ (tc ∙round) of λ
          where
          (yes eq) → here eq
          (no ¬eq) → case (tc′ ∙round) ≟ (te ∙round) of λ
            where
            (yes eq) → ⊥-elim $
              ¬tc (tc′ , eq , (amap (map₂ (subst (λ ◆ → _ ∈ (Timeout (te , ◆) ∷ ms)) (sym mtc≡))) p))
            (no ¬eq) → there $ r .complete {tc′} $ formedTC $
              azipWith (λ where ((mtc , te∈) , refl) → mtc , tail (λ where refl → ¬eq refl) te∈ )
                       (p , getAllRound tc′)
        (receivedTC (here (tc∈-Timeout refl))) → here refl
        (receivedTC (there p)) → there $ r .complete $ receivedTC p
      }
... | yes (tc , refl , tes) | nothing = tc ∷ ts , record
      { sound = λ where
        (here refl) → formedTC (amap (map₂ (subst (λ ◆ → _ ∈ (Timeout (te , ◆) ∷ ms)) mtc≡)) tes)
        (there tc∈) → tc∈-monotonic (r .sound tc∈)
      ; complete =  λ where
        {tc′} (formedTC p) → case (tc′ ∙round) ≟ (te ∙round) of λ
          where
          (yes eq) → here eq
          (no ¬eq) → there $ r .complete $ formedTC {tc′} $
            azipWith (λ where ((mtc , te∈) , refl) → mtc , tail (λ where refl → ¬eq refl) te∈ )
               (p , getAllRound tc′)
        (receivedTC (here (tc∈-Timeout ())))
        (receivedTC (there p)) → there $ r .complete (receivedTC p)
      }
... | yes (tc , refl , tes) | just tc′ = tc ∷ tc′ ∷ ts , record
      { sound = λ where
        (here refl) → formedTC (amap (map₂ (subst (λ ◆ → _ ∈ (Timeout (te , ◆) ∷ ms)) mtc≡)) tes)
        (there (here refl)) → receivedTC (here (tc∈-Timeout refl))
        (there (there tc∈)) → tc∈-monotonic $ r .sound tc∈
      ; complete = λ where
        {tc} (formedTC p) → case (tc ∙round) ≟ (te ∙round) of λ
          where
          (yes eq) → here eq
          (no ¬eq) → there $′ there $′ r .complete {tc} $ formedTC $
            azipWith (λ where ((mtc , te∈) , refl) → mtc , tail (λ where refl → ¬eq refl) te∈ )
                       (p , getAllRound tc)
        (receivedTC (here (tc∈-Timeout refl))) → there $′ here refl
        (receivedTC (there p)) → there $′ there $ r .complete $ receivedTC p
      }

module _ (ms : Messages) (let qs , r = allTCs⁺ ms) where
  allTCs : TCs
  allTCs = qs

  open AllTCsOf r public renaming
    ( sound    to allTCs-sound
    ; complete to allTCs-complete
    )

instance
  Dec-AllTC : ∀ {r} → AllTC (λ tc → tc ∙round < r) ⁇¹
  Dec-AllTC {r = r} {x = ms} .dec = mapDec All⇒AllTC AllTC⇒All dec
    where
    P = λ tc → tc ∙round < r

    All⇒AllTC : All P (allTCs ms) → AllTC P ms
    All⇒AllTC allP = mk (lookup (L.All.map⁺ allP) ∘′ allTCs-complete ms)

    AllTC⇒All : AllTC P ms → All P (allTCs ms)
    AllTC⇒All (mk allP) = L.All.tabulate (allP ∘ allTCs-sound _)
```
