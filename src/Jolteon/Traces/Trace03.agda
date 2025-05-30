module Jolteon.Traces.Trace03 where

open import Prelude
open import Jolteon.Traces.Core

s₃′ : GlobalState
s₃′ =
  record s₃
  { currentTime   = 28
  ; networkBuffer = []
  ; stateMap      =
    ⦅ 3 , 3 , qc₂ , nothing , AdvancingRound , ldb₃ , [ v₁ 𝔹 ⨾ v₃ 𝕃 ⨾ v₃ 𝔸 ] , [ b₁ ] , just 25 , false , false ⦆
  ∷ ⦅ 3 , 3 , qc₂ , nothing , EnteringRound , db₃ , [] , [ b₁ ] , nothing , false , true ⦆
  ∷ ⦅ 3 , 3 , qc₂ , nothing , EnteringRound , db₃ , [] , [ b₁ ] , nothing , false , true ⦆
  ∷ []
  }

s₃″ : GlobalState
s₃″ =
  record s₃′
  { stateMap      =
    ⦅ 3 , 3 , qc₂ , nothing , AdvancingRound , ldb₃ , [ v₁ 𝔹 ⨾ v₃ 𝕃 ⨾ v₃ 𝔸 ] , [ b₁ ] , just 25 , false , false ⦆
  ∷ ⦅ 3 , 3 , qc₂ , nothing , Receiving , db₃ , [] , [ b₁ ] , just 40 , false , false ⦆
  ∷ ⦅ 3 , 3 , qc₂ , nothing , Receiving , db₃ , [] , [ b₁ ] , just 40 , false , false ⦆
  ∷ []
  }

s₃‴ : GlobalState
s₃‴ =
  record s₃″
  { currentTime = 34
  ; history     = t₂ ∷ h₃
  ; stateMap    =
    ⦅ 4 , 3 , qc₂ , nothing , Receiving , ldb₃ , [ v₁ 𝔹 ⨾ v₃ 𝕃 ⨾ v₃ 𝔸 ⨾ t₂ ] , [ b₁ ] , nothing , true , false ⦆
  ∷ ⦅ 3 , 3 , qc₂ , nothing , Receiving , db₃ , [ t₂ ] , [ b₁ ] , just 40 , false , false ⦆
  ∷ ⦅ 3 , 3 , qc₂ , nothing , Receiving , db₃ , [ t₂ ] , [ b₁ ] , just 40 , false , false ⦆
  ∷ []
  }

s₃⁗ : GlobalState
s₃⁗ =
  record s₃‴
  { stateMap =
    ⦅ 4 , 3 , qc₂ , nothing , Receiving , t₂ ∷ ldb₃ , [ v₁ 𝔹 ⨾ v₃ 𝕃 ⨾ v₃ 𝔸 ] , [ b₁ ] , nothing , true , false ⦆
  ∷ ⦅ 3 , 3 , qc₂ , nothing , AdvancingRound , t₂ ∷ db₃ , [] , [ b₁ ] , just 40 , false , false ⦆
  ∷ ⦅ 3 , 3 , qc₂ , nothing , AdvancingRound , t₂ ∷ db₃ , [] , [ b₁ ] , just 40 , false , false ⦆
  ∷ []
  }

s₃⁗' : GlobalState
s₃⁗' =
  record
  { currentTime   = 46
  ; history       = t₃ ∷ t₂ ∷ h₃
  ; networkBuffer = []
  ; stateMap      =
    ⦅ 4 , 4 , qc₂ , just tc₁ , EnteringRound , ldb₄ , [ v₁ 𝔹 ⨾ v₃ 𝕃 ⨾ v₃ 𝔸 ] , [ b₁ ] , nothing , false , true ⦆
  ∷ ⦅ 3 , 3 , qc₂ , nothing , Receiving , t₂ ∷ db₃ , [ t₃ ] , [ b₁ ] , just 40 , false , false ⦆
  ∷ ⦅ 4 , 3 , qc₂ , nothing , AdvancingRound , t₃ ∷ t₂ ∷ db₃ , [] , [ b₁ ] , nothing , true , false ⦆
  ∷ []
  }

opaque
  unfolding blockPayload chainPayload

  trace03 : s₃ —↠ s₃′
  trace03 =
    begin
      s₃
    —→⟨ Deliver? (24 , 𝕃 , v₃ 𝕃) ⟩
      _
    —→⟨ Deliver? (24 , 𝕃 , v₃ 𝔸) ⟩
      _
    —→⟨ WaitUntil? 28 ⟩
      s₃′
    ∎

  -- 𝕃 has timed out, but 𝔸 and 𝔹 can make a step.
  _ : s₃′ —↠ s₃″
  _ =
    begin
      s₃′
    —→⟨ 𝔸 :InitNoTC? ⟩
      record s₃′
      { stateMap      =
        _
      ∷ ⦅ 3 , 3 , qc₂ , nothing , Proposing , db₃ , [] , [ b₁ ] , just 40 , false , false ⦆
      ∷ _
      ∷ []
      }
    —→⟨ 𝔸 :ProposeBlockNoOp? ⟩
      _
    —→⟨ 𝔹 :InitNoTC? ⟩
      record s₃′
      { stateMap      =
        _
      ∷ _
      ∷ ⦅ 3 , 3 , qc₂ , nothing , Proposing , db₃ , [] , [ b₁ ] , just 40 , false , false ⦆
      ∷ []
      }
    —→⟨ 𝔹 :ProposeBlockNoOp? ⟩
      s₃″
    ∎

  -- 𝕃 times out
  _ : s₃″ —↠ s₃‴
  _ = begin
      s₃″
    —→⟨ 𝕃 :AdvanceRoundNoOp? ⟩
      record s₃″
      { stateMap      =
        ⦅ 3 , 3 , qc₂ , nothing , Locking , ldb₃ , [ v₁ 𝔹 ⨾ v₃ 𝕃 ⨾ v₃ 𝔸 ] , [ b₁ ] , just 25 , false , false ⦆
      ∷ ⦅ 3 , 3 , qc₂ , nothing , Receiving , db₃ , [] , [ b₁ ] , just 40 , false , false ⦆
      ∷ ⦅ 3 , 3 , qc₂ , nothing , Receiving , db₃ , [] , [ b₁ ] , just 40 , false , false ⦆
      ∷ []
      }
    —→⟨ 𝕃 :Lock? ⟩
      record s₃″
      { stateMap      =
        ⦅ 3 , 3 , qc₂ , nothing , Committing , ldb₃ , [ v₁ 𝔹 ⨾ v₃ 𝕃 ⨾ v₃ 𝔸 ] , [ b₁ ] , just 25 , false , false ⦆
      ∷ ⦅ 3 , 3 , qc₂ , nothing , Receiving , db₃ , [] , [ b₁ ] , just 40 , false , false ⦆
      ∷ ⦅ 3 , 3 , qc₂ , nothing , Receiving , db₃ , [] , [ b₁ ] , just 40 , false , false ⦆
      ∷ []
      }
    —→⟨ 𝕃 :CommitNoOp? ⟩
      _
    —→⟨ 𝕃 :VoteBlockNoOp? ⟩
      _
    —→⟨ 𝕃 :TimerExpired? ⟩
      record s₃″
      { history       = t₂ ∷ h₃
      ; networkBuffer = [ 28 , 𝕃 , t₂ ⨾ 28 , 𝔸 , t₂ ⨾ 28 , 𝔹 , t₂ ]
      ; stateMap      =
        ⦅ 4 , 3 , qc₂ , nothing , Receiving , ldb₃ , [ v₁ 𝔹 ⨾ v₃ 𝕃 ⨾ v₃ 𝔸 ] , [ b₁ ] , nothing , true , false ⦆
      ∷ ⦅ 3 , 3 , qc₂ , nothing , Receiving , db₃ , [] , [ b₁ ] , just 40 , false , false ⦆
      ∷ ⦅ 3 , 3 , qc₂ , nothing , Receiving , db₃ , [] , [ b₁ ] , just 40 , false , false ⦆
      ∷ []
      }
    —→⟨ Deliver? (28 , 𝕃 , t₂) ⟩
      _
    —→⟨ Deliver? (28 , 𝔸 , t₂) ⟩
      _
    —→⟨ Deliver? (28 , 𝔹 , t₂) ⟩
      _
    —→⟨ WaitUntil? 34 ⟩
      s₃‴
    ∎

  _ : s₃‴ —↠ s₃⁗
  _ =
    begin
      s₃‴
    —→⟨ 𝕃 :RegisterTimeout? tm₂ ⟩
      record s₃‴
      { stateMap      =
        ⦅ 4 , 3 , qc₂ , nothing , AdvancingRound , t₂ ∷ ldb₃ , [ v₁ 𝔹 ⨾ v₃ 𝕃 ⨾ v₃ 𝔸 ] , [ b₁ ] , nothing , true , false ⦆
      ∷ ⦅ 3 , 3 , qc₂ , nothing , Receiving , db₃ , [ t₂ ] , [ b₁ ] , just 40 , false , false ⦆
      ∷ ⦅ 3 , 3 , qc₂ , nothing , Receiving , db₃ , [ t₂ ] , [ b₁ ] , just 40 , false , false ⦆
      ∷ []
      }
    —→⟨ 𝔸 :RegisterTimeout? tm₂ ⟩
      record s₃‴
      { stateMap      =
        ⦅ 4 , 3 , qc₂ , nothing , AdvancingRound , t₂ ∷ ldb₃ , [ v₁ 𝔹 ⨾ v₃ 𝕃 ⨾ v₃ 𝔸 ] , [ b₁ ] , nothing , true , false ⦆
      ∷ ⦅ 3 , 3 , qc₂ , nothing , AdvancingRound , t₂ ∷  db₃ , [] , [ b₁ ] , just 40 , false , false ⦆
      ∷ ⦅ 3 , 3 , qc₂ , nothing , Receiving , db₃ , [ t₂ ] , [ b₁ ] , just 40 , false , false ⦆
      ∷ []
      }
    —→⟨ 𝔹 :RegisterTimeout? tm₂ ⟩
      record s₃‴
      { stateMap      =
        ⦅ 4 , 3 , qc₂ , nothing , AdvancingRound , t₂ ∷ ldb₃ , [ v₁ 𝔹 ⨾ v₃ 𝕃 ⨾ v₃ 𝔸 ] , [ b₁ ] , nothing , true , false ⦆
      ∷ ⦅ 3 , 3 , qc₂ , nothing , AdvancingRound , t₂ ∷ db₃ , [] , [ b₁ ] , just 40 , false , false ⦆
      ∷ ⦅ 3 , 3 , qc₂ , nothing , AdvancingRound , t₂ ∷ db₃ , [] , [ b₁ ] , just 40 , false , false ⦆
      ∷ []
      }
    —→⟨ 𝕃 :AdvanceRoundNoOp? ⟩
      record s₃‴
      { stateMap      =
        ⦅ 4 , 3 , qc₂ , nothing , Locking , t₂ ∷ ldb₃ , [ v₁ 𝔹 ⨾ v₃ 𝕃 ⨾ v₃ 𝔸 ] , [ b₁ ] , nothing , true , false ⦆
      ∷ ⦅ 3 , 3 , qc₂ , nothing , AdvancingRound , t₂ ∷ db₃ , [] , [ b₁ ] , just 40 , false , false ⦆
      ∷ ⦅ 3 , 3 , qc₂ , nothing , AdvancingRound , t₂ ∷ db₃ , [] , [ b₁ ] , just 40 , false , false ⦆
      ∷ []
      }
    —→⟨ 𝕃 :Lock? ⟩
      record s₃‴
      { stateMap =
        ⦅ 4 , 3 , qc₂ , nothing , Committing , t₂ ∷ ldb₃ , [ v₁ 𝔹 ⨾ v₃ 𝕃 ⨾ v₃ 𝔸 ] , [ b₁ ] , nothing , true , false ⦆
      ∷ _
      ∷ _
      ∷ []
      }
    —→⟨ 𝕃 :CommitNoOp? ⟩
      _
    —→⟨ 𝕃 :VoteBlockNoOp? ⟩
      s₃⁗
    ∎

  _ : s₃⁗ —↠ s₃⁗'
  _ =
    begin
      s₃⁗
    —→⟨ 𝔸 :AdvanceRoundNoOp? ⟩
      _
    —→⟨ 𝔸 :Lock? ⟩
      record s₃‴
      { stateMap =
        ⦅ 4 , 3 , qc₂ , nothing , Receiving , t₂ ∷ ldb₃ , [ v₁ 𝔹 ⨾ v₃ 𝕃 ⨾ v₃ 𝔸 ] , [ b₁ ] , nothing , true , false ⦆
      ∷ ⦅ 3 , 3 , qc₂ , nothing , Committing , t₂ ∷ db₃ , [] , [ b₁ ] , just 40 , false , false ⦆
      ∷ ⦅ 3 , 3 , qc₂ , nothing , AdvancingRound , t₂ ∷ db₃ , [] , [ b₁ ] , just 40 , false , false ⦆
      ∷ []
      }
    —→⟨ 𝔸 :CommitNoOp? ⟩
      record s₃‴
      { stateMap =
        ⦅ 4 , 3 , qc₂ , nothing , Receiving , t₂ ∷ ldb₃ , [ v₁ 𝔹 ⨾ v₃ 𝕃 ⨾ v₃ 𝔸 ] , [ b₁ ] , nothing , true , false ⦆
      ∷ ⦅ 3 , 3 , qc₂ , nothing , Voting , t₂ ∷ db₃ , [] , [ b₁ ] , just 40 , false , false ⦆
      ∷ ⦅ 3 , 3 , qc₂ , nothing , AdvancingRound , t₂ ∷ db₃ , [] , [ b₁ ] , just 40 , false , false ⦆
      ∷ []
      }
    —→⟨ 𝔸 :VoteBlockNoOp? ⟩
      record s₃‴
      { stateMap =
        ⦅ 4 , 3 , qc₂ , nothing , Receiving , t₂ ∷ ldb₃ , [ v₁ 𝔹 ⨾ v₃ 𝕃 ⨾ v₃ 𝔸 ] , [ b₁ ] , nothing , true , false ⦆
      ∷ ⦅ 3 , 3 , qc₂ , nothing , Receiving , t₂ ∷ db₃ , [] , [ b₁ ] , just 40 , false , false ⦆
      ∷ ⦅ 3 , 3 , qc₂ , nothing , AdvancingRound , t₂ ∷ db₃ , [] , [ b₁ ] , just 40 , false , false ⦆
      ∷ []
      }
    —→⟨ WaitUntil? 40 ⟩
      record s₃⁗
      { currentTime = 40
      ; stateMap    =
        ⦅ 4 , 3 , qc₂ , nothing , Receiving , t₂ ∷ ldb₃ , [ v₁ 𝔹 ⨾ v₃ 𝕃 ⨾ v₃ 𝔸 ] , [ b₁ ] , nothing , true , false ⦆
      ∷ ⦅ 3 , 3 , qc₂ , nothing , Receiving , t₂ ∷ db₃ , [] , [ b₁ ] , just 40 , false , false ⦆
      ∷ ⦅ 3 , 3 , qc₂ , nothing , AdvancingRound , t₂ ∷ db₃ , [] , [ b₁ ] , just 40 , false , false ⦆
      ∷ []
      }
    —→⟨ 𝔹 :AdvanceRoundNoOp? ⟩
      record s₃⁗
      { currentTime = 40
      ; stateMap    =
        ⦅ 4 , 3 , qc₂ , nothing , Receiving , t₂ ∷ ldb₃ , [ v₁ 𝔹 ⨾ v₃ 𝕃 ⨾ v₃ 𝔸 ] , [ b₁ ] , nothing , true , false ⦆
      ∷ ⦅ 3 , 3 , qc₂ , nothing , Receiving , t₂ ∷ db₃ , [] , [ b₁ ] , just 40 , false , false ⦆
      ∷ ⦅ 3 , 3 , qc₂ , nothing , Locking , t₂ ∷ db₃ , [] , [ b₁ ] , just 40 , false , false ⦆
      ∷ []
      }
    —→⟨ 𝔹 :Lock? ⟩
      record s₃⁗
      { currentTime = 40
      ; stateMap    =
        ⦅ 4 , 3 , qc₂ , nothing , Receiving , t₂ ∷ ldb₃ , [ v₁ 𝔹 ⨾ v₃ 𝕃 ⨾ v₃ 𝔸 ] , [ b₁ ] , nothing , true , false ⦆
      ∷ ⦅ 3 , 3 , qc₂ , nothing , Receiving , t₂ ∷ db₃ , [] , [ b₁ ] , just 40 , false , false ⦆
      ∷ ⦅ 3 , 3 , qc₂ , nothing , Committing , t₂ ∷ db₃ , [] , [ b₁ ] , just 40 , false , false ⦆
      ∷ []
      }
    —→⟨ 𝔹 :CommitNoOp? ⟩
      record s₃⁗
      { currentTime = 40
      ; stateMap    =
        ⦅ 4 , 3 , qc₂ , nothing , Receiving , t₂ ∷ ldb₃ , [ v₁ 𝔹 ⨾ v₃ 𝕃 ⨾ v₃ 𝔸 ] , [ b₁ ] , nothing , true , false ⦆
      ∷ ⦅ 3 , 3 , qc₂ , nothing , Receiving , t₂ ∷ db₃ , [] , [ b₁ ] , just 40 , false , false ⦆
      ∷ ⦅ 3 , 3 , qc₂ , nothing , Voting , t₂ ∷ db₃ , [] , [ b₁ ] , just 40 , false , false ⦆
      ∷ []
      }
    —→⟨ 𝔹 :VoteBlockNoOp? ⟩
      record s₃⁗
      { currentTime = 40
      ; stateMap    =
        ⦅ 4 , 3 , qc₂ , nothing , Receiving , t₂ ∷ ldb₃ , [ v₁ 𝔹 ⨾ v₃ 𝕃 ⨾ v₃ 𝔸 ] , [ b₁ ] , nothing , true , false ⦆
      ∷ ⦅ 3 , 3 , qc₂ , nothing , Receiving , t₂ ∷ db₃ , [] , [ b₁ ] , just 40 , false , false ⦆
      ∷ ⦅ 3 , 3 , qc₂ , nothing , Receiving , t₂ ∷ db₃ , [] , [ b₁ ] , just 40 , false , false ⦆
      ∷ []
      }
    —→⟨ 𝔹 :TimerExpired? ⟩
      record
      { currentTime   = 40
      ; history       = t₃ ∷ t₂ ∷ h₃
      ; networkBuffer = [ 40 , 𝕃 , t₃ ⨾ 40 , 𝔸 , t₃ ⨾ 40 , 𝔹 , t₃ ]
      ; stateMap      =
        ⦅ 4 , 3 , qc₂ , nothing , Receiving , t₂ ∷ ldb₃ , [ v₁ 𝔹 ⨾ v₃ 𝕃 ⨾ v₃ 𝔸 ] , [ b₁ ] , nothing , true , false ⦆
      ∷ ⦅ 3 , 3 , qc₂ , nothing , Receiving , t₂ ∷ db₃ , [] , [ b₁ ] , just 40 , false , false ⦆
      ∷ ⦅ 4 , 3 , qc₂ , nothing , Receiving , t₂ ∷ db₃ , [] , [ b₁ ] , nothing , true , false ⦆
      ∷ []
      }
    —→⟨ Deliver? (40 , 𝕃 , t₃) ⟩
      _
    —→⟨ Deliver? (40 , 𝔸 , t₃) ⟩
      _
    —→⟨ Deliver? (40 , 𝔹 , t₃) ⟩
      _
    —→⟨ WaitUntil? 46 ⟩
      record
      { currentTime   = 46
      ; history       = t₃ ∷ t₂ ∷ h₃
      ; networkBuffer = []
      ; stateMap      =
        ⦅ 4 , 3 , qc₂ , nothing , Receiving , t₂ ∷ ldb₃ , [ v₁ 𝔹 ⨾ v₃ 𝕃 ⨾ v₃ 𝔸 ⨾ t₃ ] , [ b₁ ] , nothing , true , false ⦆
      ∷ ⦅ 3 , 3 , qc₂ , nothing , Receiving , t₂ ∷ db₃ , [ t₃ ] , [ b₁ ] , just 40 , false , false ⦆
      ∷ ⦅ 4 , 3 , qc₂ , nothing , Receiving , t₂ ∷ db₃ , [ t₃ ] , [ b₁ ] , nothing , true , false ⦆
      ∷ []
      }
    —→⟨ 𝕃 :RegisterTimeout? tm₃ ⟩
      _
    —→⟨ 𝕃 :AdvanceRoundTC? tc₁ ⟩
      record
      { currentTime   = 46
      ; history       = t₃ ∷ t₂ ∷ h₃
      ; networkBuffer = []
      ; stateMap      =
        ⦅ 4 , 4 , qc₂ , just tc₁ , AdvancingRound , ldb₄ , [ v₁ 𝔹 ⨾ v₃ 𝕃 ⨾ v₃ 𝔸 ] , [ b₁ ] , nothing , false , true ⦆
      ∷ ⦅ 3 , 3 , qc₂ , nothing , Receiving , t₂ ∷ db₃ , [ t₃ ] , [ b₁ ] , just 40 , false , false ⦆
      ∷ ⦅ 4 , 3 , qc₂ , nothing , Receiving , t₂ ∷ db₃ , [ t₃ ] , [ b₁ ] , nothing , true , false ⦆
      ∷ []
      }
    —→⟨ 𝕃 :AdvanceRoundNoOp? ⟩
      record
      { currentTime   = 46
      ; history       = t₃ ∷ t₂ ∷ h₃
      ; networkBuffer = []
      ; stateMap      =
        ⦅ 4 , 4 , qc₂ , just tc₁ , Locking , ldb₄ , [ v₁ 𝔹 ⨾ v₃ 𝕃 ⨾ v₃ 𝔸 ] , [ b₁ ] , nothing , false , true ⦆
      ∷ ⦅ 3 , 3 , qc₂ , nothing , Receiving , t₂ ∷ db₃ , [ t₃ ] , [ b₁ ] , just 40 , false , false ⦆
      ∷ ⦅ 4 , 3 , qc₂ , nothing , Receiving , t₂ ∷ db₃ , [ t₃ ] , [ b₁ ] , nothing , true , false ⦆
      ∷ []
      }
    —→⟨ 𝕃 :Lock? ⟩
      record
      { currentTime   = 46
      ; history       = t₃ ∷ t₂ ∷ h₃
      ; networkBuffer = []
      ; stateMap      =
        ⦅ 4 , 4 , qc₂ , just tc₁ , Committing , ldb₄ , [ v₁ 𝔹 ⨾ v₃ 𝕃 ⨾ v₃ 𝔸 ] , [ b₁ ] , nothing , false , true ⦆
      ∷ ⦅ 3 , 3 , qc₂ , nothing , Receiving , t₂ ∷ db₃ , [ t₃ ] , [ b₁ ] , just 40 , false , false ⦆
      ∷ ⦅ 4 , 3 , qc₂ , nothing , Receiving , t₂ ∷ db₃ , [ t₃ ] , [ b₁ ] , nothing , true , false ⦆
      ∷ []
      }
    —→⟨ 𝕃 :CommitNoOp? ⟩
      record
      { currentTime   = 46
      ; history       = t₃ ∷ t₂ ∷ h₃
      ; networkBuffer = []
      ; stateMap      =
        ⦅ 4 , 4 , qc₂ , just tc₁ , Voting , ldb₄ , [ v₁ 𝔹 ⨾ v₃ 𝕃 ⨾ v₃ 𝔸 ] , [ b₁ ] , nothing , false , true ⦆
      ∷ ⦅ 3 , 3 , qc₂ , nothing , Receiving , t₂ ∷ db₃ , [ t₃ ] , [ b₁ ] , just 40 , false , false ⦆
      ∷ ⦅ 4 , 3 , qc₂ , nothing , Receiving , t₂ ∷ db₃ , [ t₃ ] , [ b₁ ] , nothing , true , false ⦆
      ∷ []
      }
    —→⟨ 𝕃 :VoteBlockNoOp? ⟩
      record
      { currentTime   = 46
      ; history       = t₃ ∷ t₂ ∷ h₃
      ; networkBuffer = []
      ; stateMap      =
        ⦅ 4 , 4 , qc₂ , just tc₁ , EnteringRound , ldb₄ , [ v₁ 𝔹 ⨾ v₃ 𝕃 ⨾ v₃ 𝔸 ] , [ b₁ ] , nothing , false , true ⦆
      ∷ ⦅ 3 , 3 , qc₂ , nothing , Receiving , t₂ ∷ db₃ , [ t₃ ] , [ b₁ ] , just 40 , false , false ⦆
      ∷ ⦅ 4 , 3 , qc₂ , nothing , Receiving , t₂ ∷ db₃ , [ t₃ ] , [ b₁ ] , nothing , true , false ⦆
      ∷ []
      }
    —→⟨ 𝔹 :RegisterTimeout? tm₃ ⟩
      s₃⁗'
    ∎

  _ : s₃⁗' —↠ s₄
  _ =
    begin
      s₃⁗'
    —→⟨ 𝔹 :AdvanceRoundTC? tc₁ ⟩
      record s₃⁗'
      { stateMap      =
        ⦅ 4 , 4 , qc₂ , just tc₁ , EnteringRound , ldb₄ , [ v₁ 𝔹 ⨾ v₃ 𝕃 ⨾ v₃ 𝔸 ] , [ b₁ ] , nothing , false , true ⦆
      ∷ ⦅ 3 , 3 , qc₂ , nothing , Receiving , t₂ ∷ db₃ , [ t₃ ] , [ b₁ ] , just 40 , false , false ⦆
      ∷ ⦅ 4 , 4 , qc₂ , just tc₁ , AdvancingRound , t₃ ∷ t₂ ∷ db₃ , [] , [ b₁ ] , nothing , false , true ⦆
      ∷ []
      }
    —→⟨ 𝔹 :AdvanceRoundNoOp? ⟩
      record s₃⁗'
      { stateMap      =
        ⦅ 4 , 4 , qc₂ , just tc₁ , EnteringRound , ldb₄ , [ v₁ 𝔹 ⨾ v₃ 𝕃 ⨾ v₃ 𝔸 ] , [ b₁ ] , nothing , false , true ⦆
      ∷ ⦅ 3 , 3 , qc₂ , nothing , Receiving , t₂ ∷ db₃ , [ t₃ ] , [ b₁ ] , just 40 , false , false ⦆
      ∷ ⦅ 4 , 4 , qc₂ , just tc₁ , Locking , t₃ ∷ t₂ ∷ db₃ , [] , [ b₁ ] , nothing , false , true ⦆
      ∷ []
      }
    —→⟨ 𝔹 :Lock? ⟩
      record s₃⁗'
      { stateMap      =
        ⦅ 4 , 4 , qc₂ , just tc₁ , EnteringRound , ldb₄ , [ v₁ 𝔹 ⨾ v₃ 𝕃 ⨾ v₃ 𝔸 ] , [ b₁ ] , nothing , false , true ⦆
      ∷ ⦅ 3 , 3 , qc₂ , nothing , Receiving , t₂ ∷ db₃ , [ t₃ ] , [ b₁ ] , just 40 , false , false ⦆
      ∷ ⦅ 4 , 4 , qc₂ , just tc₁ , Committing , t₃ ∷ t₂ ∷ db₃ , [] , [ b₁ ] , nothing , false , true ⦆
      ∷ []
      }
    —→⟨ 𝔹 :CommitNoOp? ⟩
      record s₃⁗'
      { stateMap      =
        ⦅ 4 , 4 , qc₂ , just tc₁ , EnteringRound , ldb₄ , [ v₁ 𝔹 ⨾ v₃ 𝕃 ⨾ v₃ 𝔸 ] , [ b₁ ] , nothing , false , true ⦆
      ∷ ⦅ 3 , 3 , qc₂ , nothing , Receiving , t₂ ∷ db₃ , [ t₃ ] , [ b₁ ] , just 40 , false , false ⦆
      ∷ ⦅ 4 , 4 , qc₂ , just tc₁ , Voting , t₃ ∷ t₂ ∷ db₃ , [] , [ b₁ ] , nothing , false , true ⦆
      ∷ []
      }
    —→⟨ 𝔹 :VoteBlockNoOp? ⟩
      record s₃⁗'
      { stateMap      =
        ⦅ 4 , 4 , qc₂ , just tc₁ , EnteringRound , ldb₄ , [ v₁ 𝔹 ⨾ v₃ 𝕃 ⨾ v₃ 𝔸 ] , [ b₁ ] , nothing , false , true ⦆
      ∷ ⦅ 3 , 3 , qc₂ , nothing , Receiving , t₂ ∷ db₃ , [ t₃ ] , [ b₁ ] , just 40 , false , false ⦆
      ∷ ⦅ 4 , 4 , qc₂ , just tc₁ , EnteringRound , t₃ ∷ t₂ ∷ db₃ , [] , [ b₁ ] , nothing , false , true ⦆
      ∷ []
      }
    —→⟨ 𝔹 :InitTC? ⟩
      record s₃⁗'
      { history       = tcf₁ ∷ t₃ ∷ t₂ ∷ h₃
      ; networkBuffer = [ 46 , 𝕃 , tcf₁ ]
      ; stateMap      =
        ⦅ 4 , 4 , qc₂ , just tc₁ , EnteringRound , ldb₄ , [ v₁ 𝔹 ⨾ v₃ 𝕃 ⨾ v₃ 𝔸 ] , [ b₁ ] , nothing , false , true ⦆
      ∷ ⦅ 3 , 3 , qc₂ , nothing , Receiving , t₂ ∷ db₃ , [ t₃ ] , [ b₁ ] , just 40 , false , false ⦆
      ∷ ⦅ 4 , 4 , qc₂ , just tc₁ , Proposing , t₃ ∷ t₂ ∷ db₃ , [] , [ b₁ ] , just 58 , false , false ⦆
      ∷ []
      }
    —→⟨ 𝔹 :ProposeBlockNoOp? ⟩
      s₄
    ∎
