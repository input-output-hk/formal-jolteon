module Jolteon.Traces.Core where

open import Prelude
open import DummyHashing
open import Hash DummyHash

open import Jolteon.Assumptions

-- Instantiate assumptions

pattern 𝕃 = fzero
pattern 𝔸 = fsuc fzero
pattern 𝔹 = fsuc (fsuc fzero)

⋯ : Assumptions
⋯ = record { go
           ; honest-majority = auto
           ; noHashCollision = λ {b}{ch} → go.noHashCollision {b}{ch}
           }
  where module go where

  hashes = DummyHashing
  open HashAssumptions hashes

  signatures = DummySigning (λ _ _ _ → true)
  open SignatureAssumptions signatures

  nodes       = 3
  nodes⁺      = auto
  τ           = 12
  Δ           = 6
  roundLeader = const 𝕃
  Honest      = const ⊤
  Dec-Honest  = ⁇ dec

  Transaction   = ⊤
  DecEq-Tx      = DecEq      Transaction ∋ it

  private
    Round = ℕ
    Pid = Fin nodes
    Transactions = List Transaction

    PayloadQC    = Hash × Round × List Pid
    PayloadTC    = Round × List (Pid × PayloadQC)
    PayloadBlock = PayloadQC × Maybe PayloadTC × ℕ × Transactions
    PayloadChain = List PayloadBlock

    digest∗ : ∀ {A : Type} → ⦃ Digestable A ⦄ → List A → Digest
    digest∗ = L.foldl _◇_ ε ∘ map digest

    digest? : ∀ {A : Type} → ⦃ Digestable A ⦄ → Maybe A → Digest
    digest? = M.maybe digest ε

    instance
      Digestable-Tx  = Digestable Transaction ∋ λ where
        .digest tx → ε
        .digest-inj → unsafePostulatedInjectivity
      Digestable-Pid = Digestable Pid ∋ λ where
        .digest → digest ∘ Fi.toℕ
        .digest-inj → unsafePostulatedInjectivity
  instance
    Digestable-Txs = Digestable Transactions ∋ λ where
      .digest → digest∗
      .digest-inj → unsafePostulatedInjectivity
    Digestable-QCᴾ = Digestable PayloadQC ∋ λ where
      .digest (h , r , pids) → digest (h , r) ◇ digest∗ pids
      .digest-inj → unsafePostulatedInjectivity
    Digestable-ℕ×QCᴾ = Digestable (ℕ × PayloadQC) ∋ λ where
      .digest (n , qc) → digest n ◇ digest qc
      .digest-inj → unsafePostulatedInjectivity
    Digestable-TCᴾ = Digestable PayloadTC ∋ λ where
      .digest (r , pqcs) → digest r ◇ let pids , qcs = L.unzip pqcs in digest∗ pids ◇ digest∗ qcs
      .digest-inj → unsafePostulatedInjectivity
    Digestable-Blockᴾ = Digestable PayloadBlock ∋ λ where
      .digest (qc , tc? , r , txs) → digest qc ◇ digest? tc? ◇ digest r ◇ digest txs
      .digest-inj → unsafePostulatedInjectivity
    Digestable-Chainᴾ = Digestable PayloadChain ∋ λ where
      .digest → digest∗
      .digest-inj → unsafePostulatedInjectivity

  postulate noHashCollision : ∀ {b : PayloadBlock} {ch : PayloadChain} → ch ♯ ≢ b ♯

  keys : Fin nodes → KeyPair
  keys = λ where
    𝕃 → mk-keyPair (# 0) (# 0)
    𝔸 → mk-keyPair (# 1) (# 1)
    𝔹 → mk-keyPair (# 2) (# 2)

open Assumptions ⋯ public
open import Jolteon ⋯ public
open import Jolteon.Decidability ⋯ public

-- Blocks and QCs
b₁ b₂ b₃ b₄ b₅ b₆ b₇ : Block
qc₁ qc₂ qc₄ qc₅ qc₆ qc₇ : QC
tc₁ : TC

b₁  = ⟨ qc₀ , nothing , 1 , [] ⟩
qc₁ = mkQC b₁ (𝕃 ∷ 𝔸 ∷ [])
b₂  = ⟨ qc₁ , nothing , 2 , [] ⟩
qc₂ = mkQC b₂ (𝕃 ∷ 𝔸 ∷ [])
b₃  = ⟨ qc₂ , nothing , 3 , [] ⟩
b₄  = ⟨ qc₂ , just tc₁ , 4 , [] ⟩
qc₄ = mkQC b₂ (𝔹 ∷ 𝔸 ∷ [])
b₅  = ⟨ qc₄ , nothing , 5 , [] ⟩
qc₅ = mkQC b₂ (𝔹 ∷ 𝔸 ∷ [])
b₆  = ⟨ qc₅ , nothing , 6 , [] ⟩
qc₆ = mkQC b₂ (𝔹 ∷ 𝔸 ∷ [])
b₇  = ⟨ qc₆ , nothing , 7 , [] ⟩
qc₇ = mkQC b₂ (𝔹 ∷ 𝔸 ∷ [])

-- Messages
p₁ p₂ p₃ p₄ t₁ t₂ t₃ tcf₁ : Message

p₁ = Propose (b₁ signed-by 𝕃)
p₂ = Propose (b₂ signed-by 𝕃)
p₃ = Propose (b₃ signed-by 𝕃)
p₄ = Propose (b₄ signed-by 𝕃)

v₁ v₂ v₃ : Pid → Message
v₁ p = Vote $ signData p (b₁ ∙blockId , b₁ ∙round)
v₂ p = Vote $ signData p (b₂ ∙blockId , b₂ ∙round)
v₃ p = Vote $ signData p (b₃ ∙blockId , b₃ ∙round)

tm₁ tm₂ tm₃ : TimeoutMessage
te₁ te₂ te₃ : TimeoutEvidence

te₁ = signData 𝔹 (1 , qc₀)
tm₁ = te₁ , nothing
t₁  = Timeout tm₁

te₂ = signData 𝕃 (3 , qc₂)
tm₂ = te₂ , nothing
t₂  = Timeout tm₂

te₃ = signData 𝔹 (3 , qc₂)
tm₃ = te₃ , nothing
t₃  = Timeout tm₃

te₄ = signData 𝔸 (3 , qc₂)
tm₄ = te₄ , nothing
t₄  = Timeout tm₄

tc₁ = mkTC 3 $ [ te₃ ⨾ te₂ ]

tcf₁ = TCFormed tc₁

-- States
s₀ = initGlobalState

h₁   = Messages ∋ [ v₂ 𝕃 ⨾ v₂ 𝔸 ⨾ p₂ ⨾ v₁ 𝔸 ⨾ v₁ 𝕃 ⨾ p₁ ]
ldb₁ = Messages ∋ [ p₂ ⨾ v₁ 𝔸 ⨾ v₁ 𝕃 ⨾ p₁ ]
s₁ = record
  { currentTime   = 10
  ; history       = h₁
  ; networkBuffer = [ 10 , 𝕃 , v₂ 𝔸 ⨾ 10 , 𝕃 , v₂ 𝕃 ]
  ; stateMap      =
    ⦅ 2 , 2 , qc₁ , nothing , Receiving , ldb₁ , [] , [] , just 20 , false , false ⦆
  ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , [ p₂ ⨾ p₁ ] , [] , [] , nothing , false , true  ⦆
  ∷ ⦅ 0 , 1 , qc₀ , nothing , AdvancingRound , [ p₁ ] , [ p₂ ] , [] , just τ , false , false ⦆
  ∷ []
  }

h₂   = Messages ∋ v₂ 𝔹 ∷ v₁ 𝔹 ∷ h₁
ldb₂ = Messages ∋ v₂ 𝕃 ∷ v₂ 𝔸 ∷ ldb₁
s₂ = record
  { currentTime   = 13
  ; history       = h₂
  ; networkBuffer = []
  ; stateMap      =
    ⦅ 2 , 3 , qc₂ , nothing , Voting , ldb₂ , [ v₁ 𝔹 ⨾ v₂ 𝔹 ] , [ b₁ ] , nothing , false , true ⦆
  ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , [ p₂ ⨾ p₁ ] , [] , [] , nothing , false , true ⦆
  ∷ ⦅ 2 , 2 , qc₁ , nothing , EnteringRound , [ p₂ ⨾ p₁ ] , [] , [] , nothing , false , true ⦆
  ∷ []
  }

h₃   = Messages ∋ v₃ 𝔸 ∷ v₃ 𝕃 ∷ v₃ 𝔹 ∷ p₃ ∷ h₂
db₃  = Messages ∋ [ p₃ ⨾ p₂ ⨾ p₁ ]
ldb₃ = Messages ∋ v₃ 𝔹 ∷ p₃ ∷ v₂ 𝔹 ∷ ldb₂
s₃ = record
    { currentTime   = 24
    ; history       = h₃
    ; networkBuffer = [ 24 , 𝕃 , v₃ 𝕃 ⨾ 24 , 𝕃 , v₃ 𝔸 ]
    ; stateMap      =
      ⦅ 3 , 3 , qc₂ , nothing , AdvancingRound , ldb₃ , [ v₁ 𝔹 ] , [ b₁ ] , just 25 , false , false ⦆
    ∷ ⦅ 3 , 3 , qc₂ , nothing , EnteringRound , db₃ , [] , [ b₁ ] , nothing , false , true ⦆
    ∷ ⦅ 3 , 3 , qc₂ , nothing , EnteringRound , db₃ , [] , [ b₁ ] , nothing , false , true ⦆
    ∷ []
    }

h₄   = Messages ∋ tcf₁ ∷ t₃ ∷ t₂ ∷ h₃
ldb₄ = Messages ∋ t₃ ∷ t₂ ∷ ldb₃
s₄ = record
    { currentTime   = 46
    ; history       = h₄
    ; networkBuffer = [ 46 , 𝕃 , tcf₁ ]
    ; stateMap      =
      ⦅ 4 , 4 , qc₂ , just tc₁ , EnteringRound  , ldb₄ , [ v₁ 𝔹 ⨾ v₃ 𝕃 ⨾ v₃ 𝔸 ] , [ b₁ ] , nothing , false , true ⦆
    ∷ ⦅ 3 , 3 , qc₂ , nothing , Receiving , t₂ ∷ db₃ , [ t₃ ] , [ b₁ ] , just 40 , false , false ⦆
    ∷ ⦅ 4 , 4 , qc₂ , just tc₁ , Receiving , t₃ ∷ t₂ ∷ db₃ , []  , [ b₁ ] , just 58 , false , false ⦆
    ∷ []
    }
