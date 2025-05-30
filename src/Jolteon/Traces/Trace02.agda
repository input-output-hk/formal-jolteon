module Jolteon.Traces.Trace02 where

open import Prelude
open import Jolteon.Traces.Core

s₂′ : GlobalState
s₂′ =
  record
  { currentTime   = 24
  ; history       = v₃ 𝔹 ∷ p₃ ∷ h₂
  ; networkBuffer = []
  ; stateMap      =
    ⦅ 2 , 3 , qc₂ , nothing , Receiving , v₂ 𝔹 ∷ ldb₂ , [ v₁ 𝔹 ⨾ p₃ ⨾ v₃ 𝔹 ] , [ b₁ ] , just 25 , false , false ⦆
  ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , [ p₂ ⨾ p₁ ] , [ p₃ ] , [] , nothing , false , true ⦆
  ∷ ⦅ 3 , 3 , qc₂ , nothing , EnteringRound , db₃ , [] , [ b₁ ] , nothing , false , true ⦆
  ∷ []
  }

s₂″ : GlobalState
s₂″ =
  record s₂′
  { history       = v₃ 𝕃 ∷ v₃ 𝔹 ∷ p₃ ∷ h₂
  ; networkBuffer = [ 24 , 𝕃 , v₃ 𝕃 ]
  ; stateMap      =
    ⦅ 3 , 3 , qc₂ , nothing , AdvancingRound , ldb₃ , [ v₁ 𝔹 ] , [ b₁ ] , just 25 , false , false ⦆
  ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , [ p₂ ⨾ p₁ ] , [ p₃ ]  , []  , nothing , false , true ⦆
  ∷ ⦅ 3 , 3 , qc₂ , nothing , EnteringRound , db₃ , []  , [ b₁ ] , nothing , false , true ⦆
  ∷ []
  }

opaque
  unfolding blockPayload chainPayload

  trace02 : s₂ —↠ s₂′
  trace02 =
    begin
      s₂
    —→⟨ 𝕃 :VoteBlockNoOp? ⟩
      s₂ ＠ 𝕃 %= (λ ls → record ls {phase = EnteringRound})
    —→⟨ 𝕃 :InitNoTC? ⟩
      s₂ ＠ 𝕃 ≔ ⦅ 2 , 3 , qc₂ , nothing , Proposing , ldb₂ , [ v₁ 𝔹 ⨾ v₂ 𝔹 ] , [ b₁ ] , just 25 , false , false ⦆
    —→⟨ 𝕃 :ProposeBlock? [] ⟩
      record s₂
      { history       = p₃ ∷ h₂
      ; networkBuffer = [ 13 , 𝕃 , p₃ ⨾ 13 , 𝔸 , p₃ ⨾ 13 , 𝔹 , p₃ ]
      ; stateMap      = s₂ .stateMap
      [ 𝕃 ]≔ ⦅ 2 , 3 , qc₂ , nothing , Receiving , ldb₂ , [ v₁ 𝔹 ⨾ v₂ 𝔹 ] , [ b₁ ] , just 25 , false , false ⦆
      }
    —→⟨ 𝔹 :InitNoTC? ⟩
      record s₂
      { history       = p₃ ∷ h₂
      ; networkBuffer = [ 13 , 𝕃 , p₃ ⨾ 13 , 𝔸 , p₃ ⨾ 13 , 𝔹 , p₃ ]
      ; stateMap      = s₂ .stateMap
      [ 𝕃 ]≔ ⦅ 2 , 3 , qc₂ , nothing , Receiving , ldb₂ , [ v₁ 𝔹 ⨾ v₂ 𝔹 ] , [ b₁ ] , just 25 , false , false ⦆
      [ 𝔹 ]≔ ⦅ 2 , 2 , qc₁ , nothing , Proposing , [ p₂ ⨾ p₁ ] , [] , [] , just 25 , false , false ⦆
      }
    —→⟨ 𝔹 :ProposeBlockNoOp? ⟩
      record s₂
      { history       = p₃ ∷ h₂
      ; networkBuffer = [ 13 , 𝕃 , p₃ ⨾ 13 , 𝔸 , p₃ ⨾ 13 , 𝔹 , p₃ ]
      ; stateMap      = s₂ .stateMap
      [ 𝕃 ]≔ ⦅ 2 , 3 , qc₂ , nothing , Receiving , ldb₂ , [ v₁ 𝔹 ⨾ v₂ 𝔹 ] , [ b₁ ] , just 25 , false , false ⦆
      [ 𝔹 ]≔ ⦅ 2 , 2 , qc₁ , nothing , Receiving , [ p₂ ⨾ p₁ ] , [] , [] , just 25 , false , false ⦆
      }
    —→⟨ Deliver? (13 , 𝕃 , p₃) ⟩
      record s₂
      { history       = p₃ ∷ h₂
      ; networkBuffer = [ 13 , 𝔸 , p₃ ⨾ 13 , 𝔹 , p₃ ]
      ; stateMap      = s₂ .stateMap
      [ 𝕃 ]≔ ⦅ 2 , 3 , qc₂ , nothing , Receiving , ldb₂ , [ v₁ 𝔹 ⨾ v₂ 𝔹 ⨾ p₃ ] , [ b₁ ] , just 25 , false , false ⦆
      [ 𝔹 ]≔ ⦅ 2 , 2 , qc₁ , nothing , Receiving , [ p₂ ⨾ p₁ ] , [] , [] , just 25 , false , false ⦆
      }
    —→⟨ Deliver? (13 , 𝔸 , p₃) ⟩
      record s₂
      { history       = p₃ ∷ h₂
      ; networkBuffer = [ 13 , 𝔹 , p₃ ]
      ; stateMap      =
        ⦅ 2 , 3 , qc₂ , nothing , Receiving , ldb₂ , [ v₁ 𝔹 ⨾ v₂ 𝔹 ⨾ p₃ ] , [ b₁ ] , just 25 , false , false ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , [ p₂ ⨾ p₁ ] , [ p₃ ] , [] , nothing , false , true ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , Receiving , [ p₂ ⨾ p₁ ] , [] , [] , just 25 , false , false ⦆
      ∷ []
      }
    —→⟨ Deliver? (13 , 𝔹 , p₃) ⟩
      record s₂
      { history       = p₃ ∷ h₂
      ; networkBuffer = []
      ; stateMap      =
        ⦅ 2 , 3 , qc₂ , nothing , Receiving , ldb₂ , [ v₁ 𝔹 ⨾ v₂ 𝔹 ⨾ p₃ ] , [ b₁ ] , just 25 , false , false ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , [ p₂ ⨾ p₁ ] , [ p₃ ] , [] , nothing , false , true ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , Receiving , [ p₂ ⨾ p₁ ] , [ p₃ ] , [] , just 25 , false , false ⦆
      ∷ []
      }
    —→⟨ WaitUntil? 19 ⟩
      record
      { currentTime   = 19
      ; history       = p₃ ∷ h₂
      ; networkBuffer = []
      ; stateMap      =
        ⦅ 2 , 3 , qc₂ , nothing , Receiving , ldb₂ , [ v₁ 𝔹 ⨾ v₂ 𝔹 ⨾ p₃ ] , [ b₁ ] , just 25 , false , false ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound  , [ p₂ ⨾ p₁ ] , [ p₃ ]  , []  , nothing , false , true ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , Receiving , [ p₂ ⨾ p₁ ] , [ p₃ ]  , []  , just 25 , false , false ⦆
      ∷ []
      }
    —→⟨ 𝔹 :RegisterProposal? ⟩
      record
      { currentTime   = 19
      ; history       = p₃ ∷ h₂
      ; networkBuffer = []
      ; stateMap      =
        ⦅ 2 , 3 , qc₂ , nothing , Receiving , ldb₂ , [ v₁ 𝔹 ⨾ v₂ 𝔹 ⨾ p₃ ] , [ b₁ ] , just 25 , false , false ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , [ p₂ ⨾ p₁ ] , [ p₃ ]  , []  , nothing , false , true ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , AdvancingRound , [ p₃ ⨾ p₂ ⨾ p₁ ] , []  , []  , just 25 , false , false ⦆
      ∷ []
      }
    —→⟨ 𝔹 :AdvanceRoundQC? qc₂ ⟩
      record
      { currentTime   = 19
      ; history       = p₃ ∷ h₂
      ; networkBuffer = []
      ; stateMap      =
        ⦅ 2 , 3 , qc₂ , nothing , Receiving , ldb₂ , _ , [ b₁ ] , just 25 , false , false ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , [ p₂ ⨾ p₁ ] , [ p₃ ]  , []  , nothing , false , true ⦆
      ∷ ⦅ 2 , 3 , qc₁ , nothing , AdvancingRound , db₃ , []  , []  , nothing , false , true ⦆
      ∷ []
      }
    —→⟨ 𝔹 :AdvanceRoundNoOp? ⟩
      record
      { currentTime   = 19
      ; history       = p₃ ∷ h₂
      ; networkBuffer = []
      ; stateMap      =
        ⦅ 2 , 3 , qc₂ , nothing , Receiving , ldb₂ , _ , [ b₁ ] , just 25 , false , false ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , [ p₂ ⨾ p₁ ] , [ p₃ ]  , []  , nothing , false , true ⦆
      ∷ ⦅ 2 , 3 , qc₁ , nothing , Locking , db₃ , []  , []  , nothing , false , true ⦆
      ∷ []
      }
    —→⟨ 𝔹 :Lock? ⟩
      record
      { currentTime   = 19
      ; history       = p₃ ∷ h₂
      ; networkBuffer = []
      ; stateMap      =
        ⦅ 2 , 3 , qc₂ , nothing , Receiving , ldb₂ , _ , [ b₁ ] , just 25 , false , false ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , [ p₂ ⨾ p₁ ] , [ p₃ ]  , []  , nothing , false , true ⦆
      ∷ ⦅ 2 , 3 , qc₂ , nothing , Committing , db₃ , []  , []  , nothing , false , true ⦆
      ∷ []
      }
      -- note that as 𝔹 is about to commit using b₂, but the current proposal is b₃.
    —→⟨ 𝔹 :Commit? [ b₂ ⨾ b₁ ] ⟩
      record
      { currentTime   = 19
      ; history       = p₃ ∷ h₂
      ; networkBuffer = []
      ; stateMap      =
        ⦅ 2 , 3 , qc₂ , nothing , Receiving , ldb₂ , _ , [ b₁ ] , just 25 , false , false ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , [ p₂ ⨾ p₁ ] , [ p₃ ]  , []  , nothing , false , true ⦆
      ∷ ⦅ 2 , 3 , qc₂ , nothing , Voting  , db₃ , []  , [ b₁ ] , nothing , false , true ⦆
      ∷ []
      }
    —→⟨ 𝔹 :VoteBlock? b₃ ⟩
      record
      { currentTime   = 19
      ; history       = v₃ 𝔹 ∷ p₃ ∷ h₂
      ; networkBuffer = [ 19 , 𝕃 , v₃ 𝔹 ]
      ; stateMap      =
        ⦅ 2 , 3 , qc₂ , nothing , Receiving , ldb₂ , _ , [ b₁ ] , just 25 , false , false ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound  , [ p₂ ⨾ p₁ ] , [ p₃ ]  , []  , nothing , false , true ⦆
      ∷ ⦅ 3 , 3 , qc₂ , nothing , EnteringRound  , db₃ , []  , [ b₁ ] , nothing , false , true ⦆
      ∷ []
      }
    —→⟨ Deliver? (19 , 𝕃 , v₃ 𝔹) ⟩
      _
    —→⟨ WaitUntil? 24 ⟩
      record
      { currentTime   = 24
      ; history       = v₃ 𝔹 ∷ p₃ ∷ h₂
      ; networkBuffer = []
      ; stateMap      =
        ⦅ 2 , 3 , qc₂ , nothing , Receiving , ldb₂ , [ v₁ 𝔹 ⨾ v₂ 𝔹 ⨾ p₃ ⨾ v₃ 𝔹 ] , [ b₁ ] , just 25 , false , false ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , [ p₂ ⨾ p₁ ] , [ p₃ ] , [] , nothing , false , true ⦆
      ∷ ⦅ 3 , 3 , qc₂ , nothing , EnteringRound , db₃ , [] , [ b₁ ] , nothing , false , true ⦆
      ∷ []
      }
    —→⟨ 𝕃 :RegisterVote? b₂ ⟩
      record
      { currentTime   = 24
      ; history       = v₃ 𝔹 ∷ p₃ ∷ h₂
      ; networkBuffer = []
      ; stateMap      =
        ⦅ 2 , 3 , qc₂ , nothing , AdvancingRound , v₂ 𝔹 ∷ ldb₂ , [ v₁ 𝔹 ⨾ p₃ ⨾ v₃ 𝔹 ] , [ b₁ ] , just 25 , false , false ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , [ p₂ ⨾ p₁ ] , [ p₃ ] , [] , nothing , false , true ⦆
      ∷ ⦅ 3 , 3 , qc₂ , nothing , EnteringRound , db₃ , [] , [ b₁ ] , nothing , false , true ⦆
      ∷ []
      }
    —→⟨ 𝕃 :AdvanceRoundNoOp? ⟩
      _
    —→⟨ 𝕃 :Lock? ⟩
      record
      { currentTime   = 24
      ; history       = v₃ 𝔹 ∷ p₃ ∷ h₂
      ; networkBuffer = []
      ; stateMap      =
        ⦅ 2 , 3 , qc₂ , nothing , Committing , v₂ 𝔹 ∷ ldb₂ , [ v₁ 𝔹 ⨾ p₃ ⨾ v₃ 𝔹 ] , [ b₁ ] , just 25 , false , false ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , [ p₂ ⨾ p₁ ] , [ p₃ ] , [] , nothing , false , true ⦆
      ∷ ⦅ 3 , 3 , qc₂ , nothing , EnteringRound , db₃ , [] , [ b₁ ] , nothing , false , true ⦆
      ∷ []
      }
    —→⟨ 𝕃 :CommitNoOp? ⟩
      _
    —→⟨ 𝕃 :VoteBlockNoOp? ⟩
      s₂′
    ∎

  _ : s₂′ —↠ s₂″
  _ =
    begin
      s₂′
    —→⟨ 𝕃 :RegisterProposal? ⟩
      record s₂′
      { stateMap      =
        ⦅ 2 , 3 , qc₂ , nothing , AdvancingRound , p₃ ∷ v₂ 𝔹 ∷ ldb₂ , [ v₁ 𝔹 ⨾ v₃ 𝔹 ] , [ b₁ ] , just 25 , false , false ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , [ p₂ ⨾ p₁ ] , [ p₃ ]  , []  , nothing , false , true ⦆
      ∷ ⦅ 3 , 3 , qc₂ , nothing , EnteringRound , db₃ , []  , [ b₁ ] , nothing , false , true ⦆
      ∷ []
      }
    —→⟨ 𝕃 :AdvanceRoundNoOp? ⟩
      _
    —→⟨ 𝕃 :Lock? ⟩
      record s₂′
      { stateMap      =
        ⦅ 2 , 3 , qc₂ , nothing , Committing , p₃ ∷ v₂ 𝔹 ∷ ldb₂ , [ v₁ 𝔹 ⨾ v₃ 𝔹 ] , [ b₁ ] , just 25 , false , false ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , [ p₂ ⨾ p₁ ] , [ p₃ ]  , []  , nothing , false , true ⦆
      ∷ ⦅ 3 , 3 , qc₂ , nothing , EnteringRound , db₃ , []  , [ b₁ ] , nothing , false , true ⦆
      ∷ []
      }
    —→⟨ 𝕃 :CommitNoOp? ⟩
      _
    —→⟨ 𝕃 :VoteBlock? b₃ ⟩
      record s₂′
      { history       = v₃ 𝕃 ∷ v₃ 𝔹 ∷ p₃ ∷ h₂
      ; networkBuffer = [ 24 , 𝕃 , v₃ 𝕃 ]
      ; stateMap      =
        ⦅ 3 , 3 , qc₂ , nothing , Receiving , p₃ ∷ v₂ 𝔹 ∷ ldb₂ , [ v₁ 𝔹 ⨾ v₃ 𝔹 ] , [ b₁ ] , just 25 , false , false ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , [ p₂ ⨾ p₁ ] , [ p₃ ]  , []  , nothing , false , true ⦆
      ∷ ⦅ 3 , 3 , qc₂ , nothing , EnteringRound , db₃ , []  , [ b₁ ] , nothing , false , true ⦆
      ∷ []
      }
    —→⟨ 𝕃 :RegisterVote? b₃ ⟩
      s₂″
    ∎

  _ : s₂″ —↠ s₃
  _ = begin
      s₂″
    —→⟨ 𝔸 :InitNoTC? ⟩
      record s₂″
      { stateMap      =
        _
      ∷ ⦅ 2 , 2 , qc₁ , nothing , Proposing , [ p₂ ⨾ p₁ ] , [ p₃ ] , [] , just 36 , false , false ⦆
      ∷ _
      ∷ []
      }
    —→⟨ 𝔸 :ProposeBlockNoOp? ⟩
      _
    —→⟨ 𝔸 :RegisterProposal? ⟩
      record s₂″
      { stateMap      =
        _
      ∷ ⦅ 2 , 2 , qc₁ , nothing , AdvancingRound , [ p₃ ⨾ p₂ ⨾ p₁ ] , [] , [] , just 36 , false , false ⦆
      ∷ _
      ∷ []
      }
    —→⟨ 𝔸 :AdvanceRoundQC? qc₂ ⟩
      record s₂″
      { stateMap      =
        _
      ∷ ⦅ 2 , 3 , qc₁ , nothing , AdvancingRound , db₃ , [] , [] , nothing , false , true ⦆
      ∷ _
      ∷ []
      }
    —→⟨ 𝔸 :AdvanceRoundNoOp? ⟩
      record s₂″
      { stateMap      =
        _
      ∷ ⦅ 2 , 3 , qc₁ , nothing , Locking , db₃ , [] , [] , nothing , false , true ⦆
      ∷ _
      ∷ []
      }
    —→⟨ 𝔸 :Lock? ⟩
      record s₂″
      { stateMap      =
        _
      ∷ ⦅ 2 , 3 , qc₂ , nothing , Committing , db₃ , [] , [] , nothing , false , true ⦆
      ∷ _
      ∷ []
      }
    —→⟨ 𝔸 :Commit? [ b₂ ⨾ b₁ ] ⟩
      record s₂″
      { stateMap      =
        _
      ∷ ⦅ 2 , 3 , qc₂ , nothing , Voting , db₃ , [] , [ b₁ ] , nothing , false , true ⦆
      ∷ _
      ∷ []
      }
    —→⟨ 𝔸 :VoteBlock? b₃ ⟩
      record s₂″
      { history       = v₃ 𝔸 ∷ v₃ 𝕃 ∷ v₃ 𝔹 ∷ p₃ ∷ h₂
      ; networkBuffer = [ 24 , 𝕃 , v₃ 𝕃 ⨾ 24 , 𝕃 , v₃ 𝔸 ]
      ; stateMap      =
        _
      ∷ ⦅ 3 , 3 , qc₂ , nothing , EnteringRound , db₃ , [] , [ b₁ ] , nothing , false , true ⦆
      ∷ _
      ∷ []
      }
   ∎
