module Jolteon.Traces.LockFuture where

open import Prelude
open import Jolteon.Traces.Core

s₂′ s₂″ : GlobalState
s₂′ =
  record s₁
  { history       = p₃ ∷ v₁ 𝔹 ∷ s₁ .history
  ; networkBuffer = []
  ; stateMap      =
    ⦅ 2 , 3 , qc₂ , nothing , Receiving , ldb₂ , [ v₁ 𝔹 ⨾ p₃ ] , [ b₁ ] , just (10 + τ) , false , false ⦆
  ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , [ p₂ ⨾ p₁ ] , [ p₃ ] , [] , nothing , false , true ⦆
  ∷ ⦅ 1 , 1 , qc₀ , nothing , AdvancingRound , [ p₂ ⨾ p₁ ]  , [ p₃ ] , [] , just τ , false , false ⦆
  ∷ []
  }

s₂″ =
  record s₂′
  { stateMap      =
    ⦅ 2 , 3 , qc₂ , nothing , Receiving , ldb₂ , [ v₁ 𝔹 ⨾ p₃ ] , [ b₁ ] , just (10 + τ) , false , false ⦆
  ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , [ p₂ ⨾ p₁ ] , [ p₃ ] , [] , nothing , false , true ⦆
  ∷ ⦅ 1 , 2 , qc₁ , nothing , Committing , [ p₂ ⨾ p₁ ]  , [ p₃ ] , [] , nothing , false , true ⦆
  ∷ []
  }

opaque
  unfolding blockPayload chainPayload

  lockFuture : s₁ —↠ s₂′
  lockFuture =
    begin
      s₁
    —→⟨ Deliver? (10 , 𝕃 , v₂ 𝔸) ⟩
      _
    —→⟨ Deliver? (10 , 𝕃 , v₂ 𝕃) ⟩
      record s₁
      { networkBuffer = []
      ; stateMap      =
        ⦅ 2 , 2 , qc₁ , nothing , Receiving , p₂ ∷ _ , [ v₂ 𝔸 ⨾ v₂ 𝕃 ]  , [] , just 20 , false , false ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound  , p₂ ∷ _ , []  , [] , nothing , false , true  ⦆
      ∷ ⦅ 0 , 1 , qc₀ , nothing , AdvancingRound , [ p₁ ] , [ p₂ ] , [] , just τ , false , false ⦆
      ∷ []
      }
    —→⟨ 𝕃 :RegisterVote? b₂ ⟩
      record s₁
      { networkBuffer = []
      ; stateMap      =
        ⦅ 2 , 2 , qc₁ , nothing , AdvancingRound , v₂ 𝔸 ∷ _ , [ v₂ 𝕃 ]  , [] , just 20 , false , false ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound  , p₂ ∷ _ , []  , [] , nothing , false , true  ⦆
      ∷ ⦅ 0 , 1 , qc₀ , nothing , AdvancingRound , [ p₁ ] , [ p₂ ] , [] , just τ , false , false ⦆
      ∷ []
      }
    —→⟨ 𝕃 :AdvanceRoundNoOp? ⟩
      _
    —→⟨ 𝕃 :Lock? ⟩
      record s₁
      { networkBuffer = []
      ; stateMap      =
        ⦅ 2 , 2 , qc₁ , nothing , Committing , v₂ 𝔸 ∷ _ , [ v₂ 𝕃 ]  , [] , just 20 , false , false ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound  , p₂ ∷ _ , []  , [] , nothing , false , true  ⦆
      ∷ ⦅ 0 , 1 , qc₀ , nothing , AdvancingRound , [ p₁ ] , [ p₂ ] , [] , just τ , false , false ⦆
      ∷ []
      }
    —→⟨ 𝕃 :CommitNoOp? ⟩
      _
    —→⟨ 𝕃 :VoteBlockNoOp? ⟩
      _
    —→⟨ 𝕃 :RegisterVote? b₂ ⟩
      record s₁
      { networkBuffer = []
      ; stateMap      =
        ⦅ 2 , 2 , qc₁ , nothing , AdvancingRound , v₂ 𝕃 ∷ v₂ 𝔸 ∷ _ , [] , [] , just 20 , false , false ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , [ p₂ ⨾ p₁ ] , [] , [] , nothing , false , true ⦆
      ∷ ⦅ 0 , 1 , qc₀ , nothing , AdvancingRound , [ p₁ ]  , [ p₂ ] , [] , just τ , false , false ⦆
      ∷ []
      }
    —→⟨ 𝕃 :AdvanceRoundQC? qc₂ ⟩
      _
    —→⟨ 𝕃 :AdvanceRoundNoOp? ⟩
      _
    —→⟨ 𝕃 :Lock? ⟩
      record s₁
      { networkBuffer = []
      ; stateMap      =
        ⦅ 2 , 3 , qc₂ , nothing , Committing , ldb₂ , [] , [] , nothing , false , true ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , [ p₂ ⨾ p₁ ] , [] , [] , nothing , false , true ⦆
      ∷ ⦅ 0 , 1 , qc₀ , nothing , AdvancingRound , [ p₁ ]  , [ p₂ ] , [] , just τ , false , false ⦆
      ∷ []
      }
    —→⟨ 𝕃 :Commit? [ b₂ ⨾ b₁ ] ⟩
      record s₁
      { networkBuffer = []
      ; stateMap      =
        ⦅ 2 , 3 , qc₂ , nothing , Voting , ldb₂ , [] , [ b₁ ] , nothing , false , true ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , [ p₂ ⨾ p₁ ] , [] , [] , nothing , false , true ⦆
      ∷ ⦅ 0 , 1 , qc₀ , nothing , AdvancingRound , [ p₁ ]  , [ p₂ ] , [] , just τ , false , false ⦆
      ∷ []
      }
    —→⟨ 𝔹 :AdvanceRoundNoOp? ⟩
      record s₁
      { networkBuffer = []
      ; stateMap      =
        ⦅ 2 , 3 , qc₂ , nothing , Voting , ldb₂ , [] , [ b₁ ] , nothing , false , true ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , [ p₂ ⨾ p₁ ] , [] , [] , nothing , false , true ⦆
      ∷ ⦅ 0 , 1 , qc₀ , nothing , Locking , [ p₁ ]  , [ p₂ ] , [] , just τ , false , false ⦆
      ∷ []
      }
    —→⟨ 𝔹 :Lock? ⟩
      record s₁
      { networkBuffer = []
      ; stateMap      =
        ⦅ 2 , 3 , qc₂ , nothing , Voting , ldb₂ , [] , [ b₁ ] , nothing , false , true ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , [ p₂ ⨾ p₁ ] , [] , [] , nothing , false , true ⦆
      ∷ ⦅ 0 , 1 , qc₀ , nothing , Committing , [ p₁ ]  , [ p₂ ] , [] , just τ , false , false ⦆
      ∷ []
      }
    —→⟨ 𝔹 :CommitNoOp? ⟩
      record s₁
      { networkBuffer = []
      ; stateMap      =
        ⦅ 2 , 3 , qc₂ , nothing , Voting , ldb₂ , [] , [ b₁ ] , nothing , false , true ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , [ p₂ ⨾ p₁ ] , [] , [] , nothing , false , true ⦆
      ∷ ⦅ 0 , 1 , qc₀ , nothing , Voting , [ p₁ ]  , [ p₂ ] , [] , just τ , false , false ⦆
      ∷ []
      }
    —→⟨ 𝔹 :VoteBlock? b₁ ⟩
      record s₁
      { history       = v₁ 𝔹 ∷ _
      ; networkBuffer = [ 10 , 𝕃 , v₁ 𝔹 ]
      ; stateMap      =
        ⦅ 2 , 3 , qc₂ , nothing , Voting , ldb₂ , [] , [ b₁ ] , nothing , false , true ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , [ p₂ ⨾ p₁ ] , [] , [] , nothing , false , true ⦆
      ∷ ⦅ 1 , 1 , qc₀ , nothing , Receiving , [ p₁ ]  , [ p₂ ] , [] , just τ , false , false ⦆
      ∷ []
      }
    —→⟨ 𝕃 :VoteBlockNoOp? ⟩
      record s₁
      { history       = v₁ 𝔹 ∷ _
      ; networkBuffer = [ 10 , 𝕃 , v₁ 𝔹 ]
      ; stateMap      =
        ⦅ 2 , 3 , qc₂ , nothing , EnteringRound , ldb₂ , [] , [ b₁ ] , nothing , false , true ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , [ p₂ ⨾ p₁ ] , [] , [] , nothing , false , true ⦆
      ∷ ⦅ 1 , 1 , qc₀ , nothing , Receiving , [ p₁ ]  , [ p₂ ] , [] , just τ , false , false ⦆
      ∷ []
      }
    —→⟨ 𝕃 :InitNoTC? ⟩
      record s₁
      { history       = v₁ 𝔹 ∷ _
      ; networkBuffer = [ 10 , 𝕃 , v₁ 𝔹 ]
      ; stateMap      =
        ⦅ 2 , 3 , qc₂ , nothing , Proposing , ldb₂ , [] , [ b₁ ] , just (10 + τ) , false , false ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , [ p₂ ⨾ p₁ ] , [] , [] , nothing , false , true ⦆
      ∷ ⦅ 1 , 1 , qc₀ , nothing , Receiving , [ p₁ ]  , [ p₂ ] , [] , just τ , false , false ⦆
      ∷ []
      }
    —→⟨ 𝕃 :ProposeBlock? [] ⟩
      record s₁
      { history       = p₃ ∷ v₁ 𝔹 ∷ _
      ; networkBuffer = [ 10 , 𝕃 , v₁ 𝔹 ⨾ 10 , 𝕃 , p₃ ⨾ 10 , 𝔸 , p₃ ⨾ 10 , 𝔹 , p₃ ]
      ; stateMap      =
        ⦅ 2 , 3 , qc₂ , nothing , Receiving , ldb₂ , [] , [ b₁ ] , just (10 + τ) , false , false ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , [ p₂ ⨾ p₁ ] , [] , [] , nothing , false , true ⦆
      ∷ ⦅ 1 , 1 , qc₀ , nothing , Receiving , [ p₁ ]  , [ p₂ ] , [] , just τ , false , false ⦆
      ∷ []
      }
    —→⟨ Deliver? (10 , 𝕃 , v₁ 𝔹) ⟩
      _
    —→⟨ Deliver? (10 , 𝕃 , p₃) ⟩
      _
    —→⟨ Deliver? (10 , 𝔸 , p₃) ⟩
      _
    —→⟨ Deliver? (10 , 𝔹 , p₃) ⟩
      record s₁
      { history       = p₃ ∷ v₁ 𝔹 ∷ _
      ; networkBuffer = []
      ; stateMap      =
        ⦅ 2 , 3 , qc₂ , nothing , Receiving , ldb₂ , [ v₁ 𝔹 ⨾ p₃ ] , [ b₁ ] , just (10 + τ) , false , false ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , [ p₂ ⨾ p₁ ] , [ p₃ ] , [] , nothing , false , true ⦆
      ∷ ⦅ 1 , 1 , qc₀ , nothing , Receiving , [ p₁ ]  , [ p₂ ⨾ p₃ ] , [] , just τ , false , false ⦆
      ∷ []
      }
  {-
    ** 𝔹 cannot register the proposal of b₃, without first having registered b₂
       ...neither register a vote for a non-registered block
    —→⟨ 𝔹 :RegisterProposal? ⟩
      record s₁
      { history       = p₃ ∷ v₁ 𝔹 ∷ _
      ; networkBuffer = []
      ; stateMap      =
        ⦅ 2 , 3 , qc₂ , nothing , Receiving , ldb₂ , [ v₁ 𝔹 ⨾ p₃ ] , [ b₁ ] , just (10 + τ) , false , false ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , [ p₂ ⨾ p₁ ] , [ p₃ ] , [] , nothing , false , true ⦆
      ∷ ⦅ 1 , 1 , qc₀ , nothing , AdvancingRound , [ p₃ ⨾ p₁ ]  , [ p₂ ] , [] , just τ , false , false ⦆
      ∷ []
      }
  -}
    —→⟨ 𝔹 :RegisterProposal? ⟩
      s₂′
    ∎

  _ : s₂′ —↠ s₂″
  _ = begin
      s₂′
  {- ** 𝔹 cannot advance using past qc₀ (since qc ∙round ≱ ls .r-cur)
    —→⟨ 𝔹 :AdvanceRoundQC? qc₀ ⟩
      record s₂′
      { stateMap      =
        ⦅ 2 , 3 , qc₂ , nothing , Receiving , ldb₂ , [ v₁ 𝔹 ⨾ p₃ ] , [ b₁ ] , just (10 + τ) , false , false ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , [ p₂ ⨾ p₁ ] , [ p₃ ] , [] , nothing , false , true ⦆
      ∷ ⦅ 1 , 1 , qc₀ , nothing , Locking , [ p₂ ⨾ p₁ ]  , [ p₃ ] , [] , nothing , false , true ⦆
      ∷ []
      }
  -}
  {- ** 𝔹 cannot advance using future qc₂ (since qc₂ ∉ ls .db)
    —→⟨ 𝔹 :AdvanceRoundQC? qc₂ ⟩
      record s₂′
      { stateMap      =
        ⦅ 2 , 3 , qc₂ , nothing , Receiving , ldb₂ , [ v₁ 𝔹 ⨾ p₃ ] , [ b₁ ] , just (10 + τ) , false , false ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , [ p₂ ⨾ p₁ ] , [ p₃ ] , [] , nothing , false , true ⦆
      ∷ ⦅ 1 , 3 , qc₀ , nothing , Locking , [ p₂ ⨾ p₁ ]  , [ p₃ ] , [] , nothing , false , true ⦆
      ∷ []
      }
  -}
    —→⟨ 𝔹 :AdvanceRoundQC? qc₁ ⟩
      record s₂′
      { stateMap      =
        ⦅ 2 , 3 , qc₂ , nothing , Receiving , ldb₂ , [ v₁ 𝔹 ⨾ p₃ ] , [ b₁ ] , just (10 + τ) , false , false ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , [ p₂ ⨾ p₁ ] , [ p₃ ] , [] , nothing , false , true ⦆
      ∷ ⦅ 1 , 2 , qc₀ , nothing , AdvancingRound , [ p₂ ⨾ p₁ ]  , [ p₃ ] , [] , nothing , false , true ⦆
      ∷ []
      }
    —→⟨ 𝔹 :AdvanceRoundNoOp? ⟩
      record s₂′
      { stateMap      =
        ⦅ 2 , 3 , qc₂ , nothing , Receiving , ldb₂ , [ v₁ 𝔹 ⨾ p₃ ] , [ b₁ ] , just (10 + τ) , false , false ⦆
      ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , [ p₂ ⨾ p₁ ] , [ p₃ ] , [] , nothing , false , true ⦆
      ∷ ⦅ 1 , 2 , qc₀ , nothing , Locking , [ p₂ ⨾ p₁ ]  , [ p₃ ] , [] , nothing , false , true ⦆
      ∷ []
      }
    —→⟨ 𝔹 :Lock? ⟩
     s₂″
    ∎
