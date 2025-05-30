module Jolteon.Traces.Trace01b where

open import Prelude
open import Jolteon.Traces.Core

private h = Messages ∋ v₁ 𝔹 ∷ s₁ .history

s₂′ s₃′ s₄′ : GlobalState
s₂′ =
  record
  { currentTime   = 13
  ; history       = h
  ; networkBuffer = []
  ; stateMap      =
    ⦅ 2 , 3 , qc₁ , nothing , Locking , [ v₂ 𝕃 ⨾ v₂ 𝔸 ⨾ p₂ ⨾ v₁ 𝔸 ⨾ v₁ 𝕃 ⨾ p₁ ] , [ v₁ 𝔹 ] , [] , nothing , false , true ⦆
  ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , [ p₂ ⨾ p₁ ] , [] , [] , nothing , false , true ⦆
  ∷ ⦅ 1 , 1 , qc₀ , nothing , Receiving , [ p₁ ]  , [ p₂ ] , [] , just τ , false , false ⦆
  ∷ []
  }
s₃′ =
  record
  { currentTime   = 13
  ; history       = t₁ ∷ h
  ; networkBuffer = [ 13 , 𝕃 , t₁ ⨾ 13 , 𝔸 , t₁ ⨾ 13 , 𝔹 , t₁ ]
  ; stateMap      =
    ⦅ 2 , 3 , qc₂ , nothing , Voting , [ v₂ 𝕃 ⨾ v₂ 𝔸 ⨾ p₂ ⨾ v₁ 𝔸 ⨾ v₁ 𝕃 ⨾ p₁ ] , [ v₁ 𝔹 ] , [ b₁ ] , nothing , false , true ⦆
  ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , [ p₂ ⨾ p₁ ] , [] , [] , nothing , false , true ⦆
  ∷ ⦅ 2 , 2 , qc₁ , nothing , Voting , [ p₂ ⨾ p₁ ] , [] , [] , nothing , false , true ⦆
  ∷ []
  }
s₄′ =
  record
  { currentTime   = 19
  ; history       = t₁ ∷ h
  ; networkBuffer = []
  ; stateMap      =
    ⦅ 2 , 3 , qc₂ , nothing , Voting , [ v₂ 𝕃 ⨾ v₂ 𝔸 ⨾ p₂ ⨾ v₁ 𝔸 ⨾ v₁ 𝕃 ⨾ p₁ ] , [ v₁ 𝔹 ⨾ t₁ ] , [ b₁ ] , nothing , false , true ⦆
  ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , [ p₂ ⨾ p₁ ]  , [ t₁ ] , [] , nothing , false , true ⦆
  ∷ ⦅ 2 , 2 , qc₁ , nothing , Voting , [ t₁ ⨾ p₂ ⨾ p₁ ] , [] , [] , just 25 , false , false ⦆
  ∷ []
  }

opaque
  unfolding blockPayload chainPayload tcPayload tePayload

  trace01b : s₁ —↠ s₂′
  trace01b =
    begin
      s₁
    —→⟨ 𝔹 :AdvanceRoundNoOp? ⟩
      s₁ ＠ 𝔹 %= (λ ls → record ls {phase = Locking})
    —→⟨ 𝔹 :Lock? ⟩
      s₁ ＠ 𝔹 %= (λ ls → record ls {phase = Committing})
    —→⟨ 𝔹 :CommitNoOp? ⟩
      s₁ ＠ 𝔹 %= (λ ls → record ls {phase = Voting})
    —→⟨ 𝔹 :VoteBlock? b₁ ⟩
      record s₁
      { history       = v₁ 𝔹 ∷ s₁ .history
      ; networkBuffer = [ 10 , 𝕃 , v₂ 𝔸 ⨾ 10 , 𝕃 , v₂ 𝕃 ⨾ 10 , 𝕃 , v₁ 𝔹 ]
      ; stateMap      = s₁ .stateMap V.[ 𝔹 ]≔ record (s₁ ＠ 𝔹) {r-vote = 1; phase = Receiving}
      }
    —→⟨ Deliver? (10 , 𝕃 , v₂ 𝔸)  ⟩
      _
    —→⟨ Deliver? (10 , 𝕃 , v₂ 𝕃)  ⟩
      _
    —→⟨ Deliver? (10 , 𝕃 , v₁ 𝔹)  ⟩
      _
    —→⟨ WaitUntil? 13 ⟩
      record s₁
      { currentTime   = 13
      ; history       = h
      ; networkBuffer = []
      ; stateMap      =
        ⦅ 2 , 2 , qc₁ , nothing , Receiving , [ p₂ ⨾ v₁ 𝔸 ⨾ v₁ 𝕃 ⨾ p₁ ] , [ v₂ 𝔸 ⨾ v₂ 𝕃 ⨾ v₁ 𝔹 ] , [] , just 20 , false , false ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , [ p₂ ⨾ p₁ ] , [] , [] , nothing , false , true ⦆
      ∷ ⦅ 1 , 1 , qc₀ , nothing , Receiving , [ p₁ ] , [ p₂ ] , [] , just τ , false , false ⦆
      ∷ []
      }
    —→⟨ 𝕃 :RegisterVote? b₂ ⟩
      record
      { currentTime   = 13
      ; history       = h
      ; networkBuffer = []
      ; stateMap      =
        ⦅ 2 , 2 , qc₁ , nothing , AdvancingRound , v₂ 𝔸 ∷ _ , [ v₂ 𝕃 ⨾ v₁ 𝔹 ] , [] , just 20 , false , false ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , [ p₂ ⨾ p₁ ] , [] , [] , nothing , false , true ⦆
      ∷ ⦅ 1 , 1 , qc₀ , nothing , Receiving , [ p₁ ]  , [ p₂ ] , [] , just τ , false , false ⦆
      ∷ []
      }
    —→⟨ 𝕃 :AdvanceRoundNoOp? ⟩
      _
    —→⟨ 𝕃 :Lock? ⟩
      record
      { currentTime   = 13
      ; history       = h
      ; networkBuffer = []
      ; stateMap      =
        ⦅ 2 , 2 , qc₁ , nothing , Committing , v₂ 𝔸 ∷ _ , [ v₂ 𝕃 ⨾ v₁ 𝔹 ] , [] , just 20 , false , false ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , [ p₂ ⨾ p₁ ] , [] , [] , nothing , false , true ⦆
      ∷ ⦅ 1 , 1 , qc₀ , nothing , Receiving , [ p₁ ]  , [ p₂ ] , [] , just τ , false , false ⦆
      ∷ []
      }
    —→⟨ 𝕃 :CommitNoOp? ⟩
      _
    —→⟨ 𝕃 :VoteBlockNoOp? ⟩
      _
    —→⟨ 𝕃 :RegisterVote? b₂ ⟩
      record
      { currentTime   = 13
      ; history       = h
      ; networkBuffer = []
      ; stateMap      =
        ⦅ 2 , 2 , qc₁ , nothing , AdvancingRound , v₂ 𝕃 ∷ _ , [ v₁ 𝔹 ] , [] , just 20 , false , false ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , [ p₂ ⨾ p₁ ] , [] , [] , nothing , false , true ⦆
      ∷ ⦅ 1 , 1 , qc₀ , nothing , Receiving , [ p₁ ]  , [ p₂ ] , [] , just τ , false , false ⦆
      ∷ []
      }
    —→⟨ 𝕃 :AdvanceRoundQC? qc₂ ⟩
      _
    —→⟨ 𝕃 :AdvanceRoundNoOp? ⟩
      s₂′
    ∎

  _ : s₂′ —↠ s₃′
  _ = begin
      s₂′
    —→⟨ 𝕃 :Lock? ⟩
      record
      { currentTime   = 13
      ; history       = h
      ; networkBuffer = []
      ; stateMap      =
        ⦅ 2 , 3 , qc₂ , nothing , Committing , v₂ 𝕃 ∷ _ , [ v₁ 𝔹 ] , [] , nothing , false , true ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , [ p₂ ⨾ p₁ ] , [] , [] , nothing , false , true ⦆
      ∷ ⦅ 1 , 1 , qc₀ , nothing , Receiving , [ p₁ ]  , [ p₂ ] , [] , just τ , false , false ⦆
      ∷ []
      }
    —→⟨ 𝕃 :Commit? [ b₂ ⨾ b₁ ] ⟩
      record
      { currentTime   = 13
      ; history       = h
      ; networkBuffer = []
      ; stateMap      =
        ⦅ 2 , 3 , qc₂ , nothing , Voting  , v₂ 𝕃 ∷ _ , [ v₁ 𝔹 ] , [ b₁ ] , nothing , false , true ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , [ p₂ ⨾ p₁ ] , [] , [] , nothing , false , true ⦆
      ∷ ⦅ 1 , 1 , qc₀ , nothing , Receiving , [ p₁ ] , [ p₂ ] , [] , just τ , false , false ⦆
      ∷ []
      }
    —→⟨ 𝔹 :TimerExpired? ⟩
      record
      { currentTime   = 13
      ; history       = t₁ ∷ h
      ; networkBuffer = [ 13 , 𝕃 , t₁ ⨾ 13 , 𝔸 , t₁ ⨾ 13 , 𝔹 , t₁ ]
      ; stateMap      =
        ⦅ 2 , 3 , qc₂ , nothing , Voting , v₂ 𝕃 ∷ _ , [ v₁ 𝔹 ] , [ b₁ ] , nothing , false , true ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , p₂ ∷ _ , [] , [] , nothing , false , true ⦆
      ∷ ⦅ 2 , 1 , qc₀ , nothing , Receiving , [ p₁ ] , [ p₂ ] , [] , nothing , true , false ⦆
      ∷ []
      }
    —→⟨ 𝔹 :RegisterProposal? ⟩
      record
      { currentTime   = 13
      ; history       = t₁ ∷ h
      ; networkBuffer = [ 13 , 𝕃 , t₁ ⨾ 13 , 𝔸 , t₁ ⨾ 13 , 𝔹 , t₁ ]
      ; stateMap      =
        ⦅ 2 , 3 , qc₂ , nothing , Voting  , v₂ 𝕃 ∷ _ , [ v₁ 𝔹 ] , [ b₁ ] , nothing , false , true ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , p₂ ∷ _  , [] , [] , nothing , false , true ⦆
      ∷ ⦅ 2 , 1 , qc₀ , nothing , AdvancingRound , [ p₂ ⨾ p₁ ] , [] , [] , nothing , true , false ⦆
      ∷ []
      }
    —→⟨ 𝔹 :AdvanceRoundQC? qc₁ ⟩
      record
      { currentTime   = 13
      ; history       = t₁ ∷ h
      ; networkBuffer = [ 13 , 𝕃 , t₁ ⨾ 13 , 𝔸 , t₁ ⨾ 13 , 𝔹 , t₁ ]
      ; stateMap      =
        ⦅ 2 , 3 , qc₂ , nothing , Voting  , v₂ 𝕃 ∷ _ , [ v₁ 𝔹 ] , [ b₁ ] , nothing , false , true ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , p₂ ∷ _  , [] , [] , nothing , false , true ⦆
      ∷ ⦅ 2 , 2 , qc₀ , nothing , AdvancingRound , [ p₂ ⨾ p₁ ] , [] , [] , nothing , false , true ⦆
      ∷ []
      }
    —→⟨ 𝔹 :AdvanceRoundNoOp? ⟩
      record
      { currentTime   = 13
      ; history       = t₁ ∷ h
      ; networkBuffer = [ 13 , 𝕃 , t₁ ⨾ 13 , 𝔸 , t₁ ⨾ 13 , 𝔹 , t₁ ]
      ; stateMap      =
        ⦅ 2 , 3 , qc₂ , nothing , Voting  , v₂ 𝕃 ∷ _ , [ v₁ 𝔹 ] , [ b₁ ] , nothing , false , true ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , p₂ ∷ _  , [] , [] , nothing , false , true ⦆
      ∷ ⦅ 2 , 2 , qc₀ , nothing , Locking , [ p₂ ⨾ p₁ ] , [] , [] , nothing , false , true ⦆
      ∷ []
      }
    —→⟨ 𝔹 :Lock? ⟩
      record
      { currentTime   = 13
      ; history       = t₁ ∷ h
      ; networkBuffer = [ 13 , 𝕃 , t₁ ⨾ 13 , 𝔸 , t₁ ⨾ 13 , 𝔹 , t₁ ]
      ; stateMap      =
        ⦅ 2 , 3 , qc₂ , nothing , Voting  , v₂ 𝕃 ∷ _ , [ v₁ 𝔹 ] , [ b₁ ] , nothing , false , true ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , p₂ ∷ _  , [] , [] , nothing , false , true ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , Committing , [ p₂ ⨾ p₁ ] , [] , [] , nothing , false , true ⦆
      ∷ []
      }
    —→⟨ 𝔹 :CommitNoOp? ⟩
      s₃′
    ∎

  _ : s₃′ —↠ s₄′
  _ = begin
      s₃′
    —→⟨ 𝔹 :VoteBlockNoOp? ⟩
      s₃′ ＠ 𝔹 %= (λ ls → record ls {phase = EnteringRound})
    —→⟨ 𝔹 :InitNoTC? ⟩
      s₃′ ＠ 𝔹 ≔ ⦅ 2 , 2 , qc₁ , nothing , Proposing , [ p₂ ⨾ p₁ ] , [] , [] , just 25 , false , false ⦆
    —→⟨ 𝔹 :ProposeBlockNoOp? ⟩
      s₃′ ＠ 𝔹 ≔ ⦅ 2 , 2 , qc₁ , nothing , Receiving , [ p₂ ⨾ p₁ ] , [] , [] , just 25 , false , false ⦆
    —→⟨ Deliver? (13 , 𝕃 , t₁) ⟩
      record
      { currentTime   = 13
      ; history       = t₁ ∷ h
      ; networkBuffer = [ 13 , 𝔸 , t₁ ⨾ 13 , 𝔹 , t₁ ]
      ; stateMap      =
        ⦅ 2 , 3 , qc₂ , nothing , Voting , v₂ 𝕃 ∷ _ , [ v₁ 𝔹 ⨾ t₁ ] , [ b₁ ] , nothing , false , true ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , p₂ ∷ _  , [] , [] , nothing , false , true ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , Receiving , [ p₂ ⨾ p₁ ] , [] , [] , just 25 , false , false ⦆
      ∷ []
      }
    —→⟨ Deliver? (13 , 𝔸 , t₁) ⟩
      record
      { currentTime   = 13
      ; history       = t₁ ∷ h
      ; networkBuffer = [ 13 , 𝔹 , t₁ ]
      ; stateMap      =
        ⦅ 2 , 3 , qc₂ , nothing , Voting , v₂ 𝕃 ∷ _ , [ v₁ 𝔹 ⨾ t₁ ] , [ b₁ ] , nothing , false , true ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , p₂ ∷ _  , [ t₁ ] , [] , nothing , false , true ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , Receiving , [ p₂ ⨾ p₁ ] , [] , [] , just 25 , false , false ⦆
      ∷ []
      }
    —→⟨ Deliver? (13 , 𝔹 , t₁) ⟩
      _
    —→⟨ WaitUntil? 19 ⟩
      record
      { currentTime   = 19
      ; history       = t₁ ∷ h
      ; networkBuffer = []
      ; stateMap      =
        ⦅ 2 , 3 , qc₂ , nothing , Voting , v₂ 𝕃 ∷ _ , [ v₁ 𝔹 ⨾ t₁ ] , [ b₁ ] , nothing , false , true ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , p₂ ∷ _  , [ t₁ ] , [] , nothing , false , true ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , Receiving , [ p₂ ⨾ p₁ ] , [ t₁ ] , [] , just 25 , false , false ⦆
      ∷ []
      }
    —→⟨ 𝔹 :RegisterTimeout? tm₁ ⟩
      record
      { currentTime   = 19
      ; history       = t₁ ∷ h
      ; networkBuffer = []
      ; stateMap      =
        ⦅ 2 , 3 , qc₂ , nothing , Voting , v₂ 𝕃 ∷ _ , [ v₁ 𝔹 ⨾ t₁ ] , [ b₁ ] , nothing , false , true ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , p₂ ∷ _  , [ t₁ ] , [] , nothing , false , true ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , AdvancingRound , [ t₁ ⨾ p₂ ⨾ p₁ ] , [] , [] , just 25 , false , false ⦆
      ∷ []
      }
    —→⟨ 𝔹 :AdvanceRoundNoOp? ⟩
      record
      { currentTime   = 19
      ; history       = t₁ ∷ h
      ; networkBuffer = []
      ; stateMap      =
        ⦅ 2 , 3 , qc₂ , nothing , Voting , v₂ 𝕃 ∷ _ , [ v₁ 𝔹 ⨾ t₁ ] , [ b₁ ] , nothing , false , true ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , p₂ ∷ _  , [ t₁ ] , [] , nothing , false , true ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , Locking , [ t₁ ⨾ p₂ ⨾ p₁ ] , [] , [] , just 25 , false , false ⦆
      ∷ []
      }
    —→⟨ 𝔹 :Lock? ⟩
      record
      { currentTime   = 19
      ; history       = t₁ ∷ h
      ; networkBuffer = []
      ; stateMap      =
        ⦅ 2 , 3 , qc₂ , nothing , Voting , v₂ 𝕃 ∷ _ , [ v₁ 𝔹 ⨾ t₁ ] , [ b₁ ] , nothing , false , true ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , p₂ ∷ _  , [ t₁ ] , [] , nothing , false , true ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , Committing , [ t₁ ⨾ p₂ ⨾ p₁ ] , [] , [] , just 25 , false , false ⦆
      ∷ []
      }
    —→⟨ 𝔹 :CommitNoOp? ⟩
      s₄′
  -- 𝔹 should not vote for b₂, since r-vote=2 ≯ b.r=2
  {-
    —→⟨ 𝔹 :VoteBlock? b₂ ⟩
      record
      { currentTime   = 19
      ; history       = v₂ 𝔹 ∷ t₁ ∷ h
      ; networkBuffer = [ 𝕃 , v₂ 𝔹 ]
      ; stateMap      =
        ⦅ 2 , 3 , qc₂ , nothing , Voting , v₂ 𝕃 ∷ _ , [ v₁ 𝔹 ⨾ t₁ ] , [ b₁ ] , nothing , false , true ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , p₂ ∷ _  , [ t₁ ] , [] , nothing , false , true ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , Receiving , [ t₁ ⨾ p₂ ⨾ p₁ ] , [] , [] , just 25 , false , false ⦆
      ∷ []
      }
  -}
    ∎
