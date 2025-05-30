{-# OPTIONS --safe #-}
open import Prelude
open import Hash
open import Jolteon.Assumptions

module Jolteon.Properties.Safety.Lemma1 (⋯ : _) (open Assumptions ⋯) where

open import Jolteon ⋯
open import Jolteon.Properties.Core ⋯
open import Jolteon.Properties.State ⋯
open import Jolteon.Properties.Votes ⋯
open import Jolteon.Properties.Steps ⋯

open import Jolteon.Properties.Safety.Core ⋯

private
  GlobalDirectCommit-broadcast : let t = s .currentTime in
    GloballyDirectCommitted s b
    ──────────────────────────────────────────────
    GloballyDirectCommitted (broadcast t menv s) b
  GlobalDirectCommit-broadcast {s}{b}{me} (B′ , r≡ , ←B , maj) =
    B′ , r≡ , ←B , maj′
    where
    maj′ :  MoreThanF-Honest B′ (broadcast (s .currentTime) me s)
    maj′ with ⟫ me
    ... | ⟫ nothing = maj
    ... | ⟫ just e  = honest-≤ (honestVotes-mono (s . history) (e ∙message)) maj

-- Lemma 1
Commit⇒GlobalDirectCommit : ∀ {s} (Rs : Reachable s) →
  -- If an honest replica successfully performs the Commit step on block B...
  Rs ∋⋯ StepCommits b
  ───────────────────────────
  -- ...then B is globally direct-committed.
  GloballyDirectCommitted s b
Commit⇒GlobalDirectCommit
  (_ , init , (_ ⟨ WaitUntil _ _ _ ⟩←— tr)) ∃step
  = Commit⇒GlobalDirectCommit (_ , init , tr) ∃step
Commit⇒GlobalDirectCommit
  (_ , init , (_ ⟨ Deliver _ ⟩←— tr)) ∃step
  = Commit⇒GlobalDirectCommit (_ , init , tr) ∃step
Commit⇒GlobalDirectCommit
  (_ , init , (_ ⟨ DishonestLocalStep {env = env} _ _ ∣ s ⟩←— tr)) ∃step
  = GlobalDirectCommit-broadcast {s = s} {menv = just env}
  $ Commit⇒GlobalDirectCommit (_ , init , tr) ∃step
Commit⇒GlobalDirectCommit {b}
  (_ , init , (_ ⟨ LocalStep {p = p} {menv = me} {ls′ = ls′} _ ⟩←— tr))
  (there ∃step)
  = GlobalDirectCommit-broadcast {s = (tr ∙end) ＠ p ≔ ls′} {b = b} {menv = me}
  $ Commit⇒GlobalDirectCommit {b = b} {s = _} (_ , init , tr) ∃step
Commit⇒GlobalDirectCommit
  ( s₀
  , s-init
  -- By the Commit condition...
  , (_ ⟨ LocalStep (Commit _
  -- ...there exists a chain B ←— QCᴮ ←— B′ ←— QCᴮ′ with B′.r = B.r + 1.
      ( final∈ {b = b} {b′ = b′} _ cb∈′
               (_ ∷ (_ ∷ _ ⊣ connects∶ b′←b″ᵢ b′←b″ᵣ _) ⊣ connects∶ b←b′ᵢ b←b′ᵣ _)
               r≡
      , _
      )) ∣ s ⟩←— tr))
  (here refl)
  = QED
  where
  -- cb∈′ : b′ -certified-∈- (s ＠ p) .db
  -- b←b′ : b′ -connects-to- b ∷ ch
  -- r≡   : b ∙round ≡ 1 + b′ ∙round
  Rs = s₀ , s-init , tr

  -- The existence of QCᴮ′ implies that f+1 honest replicas did vote for B′.
  maj : MoreThanF-Honest b′ s
  maj with ⟫ certified {qc = qcᵇ′} qcᵇ′∈ cb′ᵢ cb′ᵣ  ← ⟫ cb∈′
    = GCB⇒MoreThanF Rs (qcᵇ′ , (cb′ᵢ , cb′ᵣ) , qc-db⊆history Rs qcᵇ′∈)

  QED : GloballyDirectCommitted s b
  QED = b′ , r≡ , (b←b′ᵢ , b←b′ᵣ) , maj
