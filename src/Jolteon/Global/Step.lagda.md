
# Jolteon Global Step

  PLAN : Allow Deliver global step to deliver many messages at once and
  advance the time there (advance by constant Δ or new constant δ s.t. δ < Δ).

<!--
```agda
{-# OPTIONS --safe #-}
open import Prelude
open import Hash

open import Jolteon.Base
open import Jolteon.Assumptions

module Jolteon.Global.Step (⋯ : _) (open Assumptions ⋯) where

open import Jolteon.Block ⋯
open import Jolteon.Message ⋯
open import Jolteon.Local.State ⋯
open import Jolteon.Local.Step ⋯
open import Jolteon.Global.State ⋯
open import Jolteon.Global.NoForging ⋯ using (NoSignatureForging)
```
-->

## State-updating functions

```agda
honestTPMessage : TPMessage → Maybe (HonestPid × Message)
honestTPMessage (_ , p , m) = case honest? p of λ where
    (yes hp) → just ((p ,· hp) , m)
    (no _)   → nothing

-- Delivers a message to replicas' inboxes.
receiveMsg : StateMap → Maybe (HonestPid × Message) → StateMap
receiveMsg sm = M.maybe′ (λ (p , m) → sm [ p ]%=′ receiveMessage m) sm

-- Deliver a message which is in transit:
--   · adds it to the corresponding inbox in a local state
--   · removes it from the network buffer
deliverMsg : ∀ s {tpm} → tpm ∈ s .networkBuffer → GlobalState
deliverMsg s {tpm} tpm∈ = record s
  { stateMap      = receiveMsg (s .stateMap) (honestTPMessage tpm)
  ; networkBuffer = s .networkBuffer L.Mem.─ tpm∈
  }

-- Takes a time and envelope and expand the broadcasted messages to n unicast messages.
-- This function broadcasts messages even to the sender (otherwise we would filter).
expandBroadcasts : Time → Envelope → TPMessages
expandBroadcasts t = expandEnv
  module _ where
  expandEnv : Envelope → TPMessages
  expandEnv = λ where
    [ m ⟩     → L.map (λ p → (t , p , m)) allPids
    [ p ∣ m ⟩ → [ (t , p , m) ]

  expandEnv-content≡ : ∀ env → All (λ (_ , _ , m) → m ≡ env .content) (expandEnv env)
  expandEnv-content≡ = λ where
    [ m ⟩     → L.All.tabulate λ x∈ → let _ , _ , eq = L.Mem.∈-map⁻ (λ p → (t , p , m)) x∈ in
                cong (proj₂ ∘ proj₂) eq
    [ p ∣ m ⟩ → refl ∷ []

broadcast : Time → Maybe Envelope → Op₁ GlobalState
broadcast t me s = record s
  { networkBuffer = maybe (λ e → s .networkBuffer ++ expandBroadcasts t e) (s .networkBuffer) me
  ; history       = L.fromMaybe (M.map _∙message me) ++ s .history
  }
```

## The (global) step relation

```agda
data _—→_ (s : GlobalState) : GlobalState → Type where

  -- An *honest* node performs a local step.
  LocalStep : ⦃ _ : Honest p ⦄ → let ls = s ＠ p; t = s .currentTime in
    (p ⦂ t ⊢ ls — menv —→ ls′)
    ────────────────────────────────────
    s —→ broadcast t menv (s ＠ p ≔ ls′)

  -- A *dishonest* node can:
  --   - Replay a message sent previously by an honest participant.
  --   - Broadcast any message signed by a dishonest participant.
  DishonestLocalStep : let m = env .content; t = s .currentTime in
    ∙ Dishonest p
    ∙ NoSignatureForging m s
      ─────────────────────────────
      s —→ broadcast t (just env) s

  -- *Deliver* a message in the network
  -- Since we may deliver any message on the network, this models
  -- non-determinism in the order that messages may arrive.
  Deliver : ∀ {tpm}
    (tpm∈ : tpm ∈ s .networkBuffer) →
    ───────────────────────────────
    s —→ deliverMsg s tpm∈

  -- We can always do nothing for a while, as long as we are
  -- still able to deliver messages in time.
  WaitUntil : ∀ t →
    ∙ All (λ (t′ , _ , _) → t ≤ t′ + Δ) (s .networkBuffer)
    ∙ currentTime s < t
      ─────────────────────────────────
      s —→ record s { currentTime = t }
```
