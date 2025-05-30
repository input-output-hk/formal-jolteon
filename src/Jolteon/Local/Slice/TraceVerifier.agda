{-# OPTIONS --safe #-}
open import Prelude; open L.Any using (index)
open import Hash

open import Jolteon.Assumptions

module Jolteon.Local.Slice.TraceVerifier
  (⋯ : _) (open Assumptions ⋯)
  (p : Pid) ⦃ hp : Honest p ⦄
  where

open import Jolteon ⋯
  hiding ( p; s; s′
         ; _—→_; _—↠_; _∎; _—→⟨_⟩_
         )
open import Jolteon.Local.Slice ⋯ p ⦃ hp ⦄
  renaming ( ss to s; ss′ to s′
           ; _—→ᴸ_ to _—→_; _—↠ᴸ_ to _—↠_; _∎ᴸ to _∎; _—→ᴸ⟨_⟩_ to _—→⟨_⟩_
           )
open import Jolteon.Decidability ⋯

-- ** actions

data Action : Type where

  -- ** local steps
  InitTC : Action
  InitNoTC : Action
  ProposeBlock : List Transaction → Action
  ProposeBlockNoOp : Action
  RegisterProposal : ℕ × Signed Block → Action
  RegisterVote : ℕ × Round × Pid × Block → Action
  RegisterTimeout : ℕ × TimeoutMessage → Action
  RegisterTC : ℕ × TC → Action
  EnoughTimeouts : Round → Action
  TimerExpired : Action
  AdvanceRoundQC : QC → Action
  AdvanceRoundTC : TC → Action
  AdvanceRoundNoOp : Action
  Lock : QC → Action
  Commit : Block × Chain → Action
  CommitNoOp : Action
  VoteBlock : Block → Action
  VoteBlockNoOp : Action

  -- ** messages
  Deliver : Message → Action

  -- ** advancing time
  WaitUntil : Time → Action

Actions = List Action

private variable
  α α′ : Action
  αs αs′ : Actions
  n n′ : ℕ

-- ** labels

private
  toℕ : ∀ {A : Type} {x} {xs : List A} → x ∈ xs → ℕ
  toℕ = Fi.toℕ ∘ index

getLabel : (s —→ s′) → Action
getLabel {s}{s′} = λ where
  (LocalStep (InitTC _ _)) → InitTC
  (LocalStep (InitNoTC _ _)) → InitNoTC
  (LocalStep (ProposeBlock {txn = txs} _ _)) → ProposeBlock txs
  (LocalStep (ProposeBlockNoOp _ _)) → ProposeBlockNoOp
  (LocalStep (RegisterProposal {sb = sb} m∈ _ _ _ _)) → RegisterProposal (toℕ m∈ , sb)
  (LocalStep (RegisterVote {r = r} {p′ = p′} {b = b} m∈ _ _ _ _ _)) → RegisterVote (toℕ m∈ , r , p′ , b)
  (LocalStep (RegisterTimeout {tm = tm} m∈ _ _ _)) → RegisterTimeout (toℕ m∈ , tm)
  (LocalStep (RegisterTC {tc = tc} m∈ _ _ _)) → RegisterTC (toℕ m∈ , tc)
  (LocalStep (EnoughTimeouts {r = r} _ _ _ _)) → EnoughTimeouts r
  (LocalStep (TimerExpired _ _)) → TimerExpired
  (LocalStep (AdvanceRoundQC {qc = qc} _ _ _)) → AdvanceRoundQC qc
  (LocalStep (AdvanceRoundTC {tc = tc} _ _ _)) → AdvanceRoundTC tc
  (LocalStep (AdvanceRoundNoOp _ _ _)) → AdvanceRoundNoOp
  (LocalStep (Lock {qc = qc} _ _)) → Lock qc
  (LocalStep (Commit {b}{ch} _ _)) → Commit (b , ch)
  (LocalStep (CommitNoOp _ _)) → CommitNoOp
  (LocalStep (VoteBlock {b = b} _ _ _)) → VoteBlock b
  (LocalStep (VoteBlockNoOp _ _)) → VoteBlockNoOp
  (Deliver m) → Deliver m
  (WaitUntil t _) → WaitUntil t

private
  getLabel≢Deliver : ∀ {m} s (st : p ⦂ s .currentTime ⊢ s .pls — menv —→ ls′) →
    getLabel (LocalStep {ss = s} st) ≢ Deliver m
  -- getLabel≢Deliver _ _ () -- ** doesn't work
  getLabel≢Deliver _ (InitTC _ _) () -- ** works!
  -- getLabel≢Deliver _ (InitNoTC _ _) () -- ** also works!!

  getLabel≢WaitUntil : ∀ s (st : p ⦂ s .currentTime ⊢ s .pls — menv —→ ls′) →
    getLabel (LocalStep {ss = s} st) ≢ WaitUntil t
  getLabel≢WaitUntil _ (InitTC _ _) ()

-- ** validity of actions

ValidAction : Action → SliceState → Type
ValidAction α s = ∃ λ s′ → ∃ λ (st : s —→ s′) → getLabel st ≡ α

private
  index? : ∀ {A : Type} n (xs : List A) →
    Dec $ ∃ λ x → ∃ λ (x∈ : x ∈ xs) → toℕ x∈ ≡ n
  index? n [] = no λ where (_ , () , _)
  index? zero (x ∷ xs) = yes (-, here refl , refl)
  index? (suc n) (x ∷ xs)
    with index? n xs
  ... | no ¬p
    = no λ where (x , there x∈ , eq) → ¬p (x , x∈ , Nat.suc-injective eq)
  ... | yes (x , x∈ , eq)
    = yes (x , there x∈ , cong suc eq)

  index≡ : ∀ {A : Type} {x y : A} n (xs : List A) →
    (x∈ : x ∈ xs) → toℕ x∈ ≡ n →
    (y∈ : y ∈ xs) → toℕ y∈ ≡ n →
    ∃ λ (eq : x ≡ y) → subst (_∈ _) eq x∈ ≡ y∈
  index≡ _ _ (here refl) refl (here refl) refl = refl , refl
  index≡ (suc n) (_ ∷ xs) (there x∈) refl (there y∈) eq
    with refl , eq ← index≡ n xs x∈ refl y∈ (Nat.suc-injective eq)
    = refl , cong there eq

private
  Propose-inj : Injective≡ Propose
  Propose-inj refl = refl

  Vote-inj : Injective≡ Vote
  Vote-inj refl = refl

  TCFormed-inj : Injective≡ TCFormed
  TCFormed-inj refl = refl

  Timeout-inj : Injective≡ Timeout
  Timeout-inj refl = refl

instance
  Dec-ValidAction : ValidAction ⁇²
  Dec-ValidAction {x = InitTC}{s} .dec
    using ls ← s .pls
    with ls .phase ≟ EnteringRound
  ... | no ph≢
    = no λ where (_ , LocalStep (InitTC ph≡ _) , refl) → ph≢ ph≡
  ... | yes ph≡
    with ls .tc-last in tc≡
  ... | nothing
    = no λ where (_ , LocalStep (InitTC _ tc≢) , refl) → case (trans (sym tc≢) tc≡) of λ ()
  ... | just tc
    = yes $ -, LocalStep (InitTC ph≡ tc≡) , refl
  Dec-ValidAction {x = InitNoTC}{s} .dec
    using ls ← s .pls
    with ls .phase ≟ EnteringRound
  ... | no ph≢
    = no λ where (_ , LocalStep (InitNoTC ph≡ _) , refl) → ph≢ ph≡
  ... | yes ph≡
    with ls .tc-last in tc≡
  ... | just tc
    = no λ where (_ , LocalStep (InitNoTC _ tc≢) , refl) → case (trans (sym tc≢) tc≡) of λ ()
  ... | nothing
    = yes $ -, LocalStep (InitNoTC ph≡ tc≡) , refl
  Dec-ValidAction {x = ProposeBlock txn}{s} .dec
    using ls ← s .pls
    with ls .phase ≟ Proposing
  ... | no ph≢
    = no λ where (_ , LocalStep (ProposeBlock ph≡ _) , refl) → ph≢ ph≡
  ... | yes ph≡
    with p ≟ currentLeader ls
  ... | no p≢
    = no λ where (_ , LocalStep (ProposeBlock _ p≡) , refl) → p≢ p≡
  ... | yes p≡
    = yes $ -, LocalStep (ProposeBlock ph≡ p≡) , refl
  Dec-ValidAction {x = ProposeBlockNoOp}{s} .dec
    using ls ← s .pls
    with ls .phase ≟ Proposing
  ... | no ph≢
    = no λ where (_ , LocalStep (ProposeBlockNoOp ph≡ _) , refl) → ph≢ ph≡
  ... | yes ph≡
    with p ≟ currentLeader ls
  ... | yes p≡
    = no λ where (_ , LocalStep (ProposeBlockNoOp _ p≢) , refl) → p≢ p≡
  ... | no p≢
    = yes $ -, LocalStep (ProposeBlockNoOp ph≡ p≢) , refl
  Dec-ValidAction {x = RegisterProposal (n , sb)}{s} .dec
    using ls ← s .pls

    with index? n (ls .inbox)
  ... | no m∉ = no λ where
    (_ , LocalStep (RegisterProposal m∈ _ _ _ _) , refl) → m∉ (-, m∈ , refl)
  ... | yes (m , m∈ , n≡)
    with m
  ... | Vote _ = no λ where
    (_ , LocalStep (RegisterProposal m∈′ _ _ _ _) , refl) →
      contradict $ index≡ _ (ls .inbox) m∈ n≡ m∈′ refl .proj₁
  ... | TCFormed _ = no λ where
    (_ , LocalStep (RegisterProposal m∈′ _ _ _ _) , refl) →
      contradict $ index≡ _ (ls .inbox) m∈ n≡ m∈′ refl .proj₁
  ... | Timeout _ = no λ where
    (_ , LocalStep (RegisterProposal m∈′ _ _ _ _) , refl) →
      contradict $ index≡ _ (ls .inbox) m∈ n≡ m∈′ refl .proj₁
  ... | Propose sb′
    with sb′ ≟ sb
  ... | no sb≢ = no λ where
    (_ , LocalStep (RegisterProposal m∈′ _ _ _ _) , refl) →
      sb≢ $ Propose-inj $ index≡ _ (ls .inbox) m∈ n≡ m∈′ refl .proj₁
  ... | yes refl
    using b ← sb .datum

    with ls .phase ≟ Receiving
  ... | no ph≢
    = no λ where (_ , LocalStep (RegisterProposal m∈ ph≡ ¬tm sb≡ vp) , refl) → ph≢ ph≡
  ... | yes ph≡
    with sb .node ≟ roundLeader (b ∙round)
  ... | no sb≢
    = no λ where (_ , LocalStep (RegisterProposal m∈ ph≡ ¬tm sb≡ vp) , refl) → sb≢ sb≡
  ... | yes sb≡
    with ¿ timedOut ls (s .currentTime) ¿
  ... | yes tm
    = no λ where (_ , LocalStep (RegisterProposal m∈ ph≡ ¬tm sb≡ vp) , refl) → ¬tm tm
  ... | no ¬tm
    with ¿ ValidProposal (ls .db) b ¿
  ... | no ¬vp
    = no λ where (_ , LocalStep (RegisterProposal m∈ ph≡ ¬tm sb≡ vp) , refl) → ¬vp vp
  ... | yes vp
    = yes $ -, LocalStep (RegisterProposal m∈ ph≡ ¬tm sb≡ vp)
             , cong (λ ◆ → RegisterProposal (◆ , _)) n≡
  Dec-ValidAction {x = RegisterVote (n , r , p′ , b)}{s} .dec
    using ls ← s .pls
    using L′ ← roundLeader (1 + r)

    with index? n (ls .inbox)
  ... | no m∉ = no λ where
    (_ , LocalStep (RegisterVote m∈ _ _ _ _ _) , refl) → m∉ (-, m∈ , refl)
  ... | yes (m₀ , m∈ , n≡)
    with m₀
  ... | Propose _ = no λ where
    (_ , LocalStep (RegisterVote m∈′ _ _ _ _ _) , refl) →
      contradict $ index≡ _ (ls .inbox) m∈ n≡ m∈′ refl .proj₁
  ... | TCFormed _ = no λ where
    (_ , LocalStep (RegisterVote m∈′ _ _ _ _ _) , refl) →
      contradict $ index≡ _ (ls .inbox) m∈ n≡ m∈′ refl .proj₁
  ... | Timeout _ = no λ where
    (_ , LocalStep (RegisterVote m∈′ _ _ _ _ _) , refl) →
      contradict $ index≡ _ (ls .inbox) m∈ n≡ m∈′ refl .proj₁
  ... | Vote vs′
    with vs′ ≟ signData p′ (b ∙blockId , r)
  ... | no vs≢ = no λ where
    (_ , LocalStep (RegisterVote m∈′ _ _ _ _ _) , refl) →
      vs≢ $ Vote-inj $ index≡ _ (ls .inbox) m∈ n≡ m∈′ refl .proj₁
  ... | yes refl
    using m ← Vote $ signData p′ (b ∙blockId , r)

    with ls .phase ≟ Receiving
  ... | no ph≢
    = no λ where (_ , LocalStep (RegisterVote _ ph≡ _ _ _ _) , refl) → ph≢ ph≡
  ... | yes ph≡
    with ¿ timedOut ls (s .currentTime) ¿
  ... | yes tm
    = no λ where (_ , LocalStep (RegisterVote _ _ ¬tm _ _ _) , refl) → ¬tm tm
  ... | no ¬tm
    with b ∙∈? ls .db
  ... | no b∉
    = no λ where (_ , LocalStep (RegisterVote _ _ _ b∈ _ _) , refl) → b∉ b∈
  ... | yes b∈
    with m ∈? ls .db
  ... | yes m∈
    = no λ where (_ , LocalStep (RegisterVote _ _ _ _ m∉ _) , refl) → m∉ m∈
  ... | no m∉
    with L′ ≟ p
  ... | no p≢
    = no λ where (_ , LocalStep (RegisterVote _ _ _ _ _ p≡) , refl) → p≢ p≡
  ... | yes p≡
    = yes $ -, LocalStep (RegisterVote m∈ ph≡ ¬tm b∈ m∉ p≡)
             , cong (λ ◆ → RegisterVote (◆ , _ , _ , _)) n≡
  Dec-ValidAction {x = RegisterTimeout (n , tm)}{s} .dec
    using ls ← s .pls

    with index? n (ls .inbox)
  ... | no m∉ = no λ where
    (_ , LocalStep (RegisterTimeout m∈ _ _ _) , refl) → m∉ (-, m∈ , refl)
  ... | yes (m₀ , m∈ , n≡)
    with m₀
  ... | Propose _ = no λ where
    (_ , LocalStep (RegisterTimeout m∈′ _ _ _) , refl) →
      contradict $ index≡ _ (ls .inbox) m∈ n≡ m∈′ refl .proj₁
  ... | Vote _ = no λ where
    (_ , LocalStep (RegisterTimeout m∈′ _ _ _) , refl) →
      contradict $ index≡ _ (ls .inbox) m∈ n≡ m∈′ refl .proj₁
  ... | TCFormed _ = no λ where
    (_ , LocalStep (RegisterTimeout m∈′ _ _ _) , refl) →
      contradict $ index≡ _ (ls .inbox) m∈ n≡ m∈′ refl .proj₁
  ... | Timeout tm′
    with tm′ ≟ tm
  ... | no tm≢ = no λ where
    (_ , LocalStep (RegisterTimeout m∈′ _ _ _) , refl) →
      tm≢ $ Timeout-inj $ index≡ _ (ls .inbox) m∈ n≡ m∈′ refl .proj₁
  ... | yes refl
    using m ← Timeout tm

    with ls .phase ≟ Receiving
  ... | no ph≢
    = no λ where (_ , LocalStep (RegisterTimeout _ ph≡ _ _) , refl) → ph≢ ph≡
  ... | yes ph≡
    with ¿ timedOut ls (s .currentTime) ¿
  ... | yes tm
    = no λ where (_ , LocalStep (RegisterTimeout _ _ ¬tm _) , refl) → ¬tm tm
  ... | no ¬tm
    with m ∈? ls .db
  ... | yes m∈
    = no λ where (_ , LocalStep (RegisterTimeout _ _ _ m∉) , refl) → m∉ m∈
  ... | no m∉
    = yes $ -, LocalStep (RegisterTimeout m∈ ph≡ ¬tm m∉)
             , cong (λ ◆ → RegisterTimeout (◆ , _)) n≡
  Dec-ValidAction {x = RegisterTC (n , tc)}{s} .dec
    using ls ← s .pls

    with index? n (ls .inbox)
  ... | no m∉ = no λ where
    (_ , LocalStep (RegisterTC m∈ _ _ _) , refl) → m∉ (-, m∈ , refl)
  ... | yes (m₀ , m∈ , n≡)
    with m₀
  ... | Propose _ = no λ where
    (_ , LocalStep (RegisterTC m∈′ _ _ _) , refl) →
      contradict $ index≡ _ (ls .inbox) m∈ n≡ m∈′ refl .proj₁
  ... | Vote _ = no λ where
    (_ , LocalStep (RegisterTC m∈′ _ _ _) , refl) →
      contradict $ index≡ _ (ls .inbox) m∈ n≡ m∈′ refl .proj₁
  ... | Timeout _ = no λ where
    (_ , LocalStep (RegisterTC m∈′ _ _ _) , refl) →
      contradict $ index≡ _ (ls .inbox) m∈ n≡ m∈′ refl .proj₁
  ... | TCFormed tc′
    with tc′ ≟ tc
  ... | no tc≢ = no λ where
    (_ , LocalStep (RegisterTC m∈′ _ _ _) , refl) →
      tc≢ $ TCFormed-inj $ index≡ _ (ls .inbox) m∈ n≡ m∈′ refl .proj₁
  ... | yes refl
    using m ← TCFormed tc

    with ls .phase ≟ Receiving
  ... | no ph≢
    = no λ where (_ , LocalStep (RegisterTC _ ph≡ _ _) , refl) → ph≢ ph≡
  ... | yes ph≡
    with ¿ timedOut ls (s .currentTime) ¿
  ... | yes tm
    = no λ where (_ , LocalStep (RegisterTC _ _ ¬tm _) , refl) → ¬tm tm
  ... | no ¬tm
    with m ∈? ls .db
  ... | yes m∈
    = no λ where (_ , LocalStep (RegisterTC _ _ _ m∉) , refl) → m∉ m∈
  ... | no m∉
    = yes $ -, LocalStep (RegisterTC m∈ ph≡ ¬tm m∉)
             , cong (λ ◆ → RegisterTC (◆ , _)) n≡
  Dec-ValidAction {x = EnoughTimeouts r}{s} .dec
    using ls  ← s .pls
    using m   ← Timeout $ signData p (ls .r-cur , ls .qc-high) , ls .tc-last
    using tms ← filter (IsTimeoutForRound? r) (ls .db)
    with ls .phase ≟ Receiving
  ... | no ph≢
    = no λ where (_ , LocalStep (EnoughTimeouts ph≡ _ _ _) , refl) → ph≢ ph≡
  ... | yes ph≡
    with ¿ timedOut ls (s .currentTime) ¿
  ... | yes tm
    = no λ where (_ , LocalStep (EnoughTimeouts _ ¬tm _ _) , refl) → ¬tm tm
  ... | no ¬tm
    with ¿ IncludesHonest tms ¿
  ... | no ¬hon
    = no λ where (_ , LocalStep (EnoughTimeouts _ _ hon _) , refl) → ¬hon hon
  ... | yes hon
    with ¿ r ≥ ls .r-cur ¿
  ... | no r≱
    = no λ where (_ , LocalStep (EnoughTimeouts _ _ _ r≥) , refl) → r≱ r≥
  ... | yes r≥
    = yes $ -, LocalStep (EnoughTimeouts ph≡ ¬tm hon r≥) , refl
  Dec-ValidAction {x = TimerExpired}{s} .dec
    using ls  ← s .pls
    using m   ← Timeout $ signData p (ls .r-cur , ls .qc-high) , ls .tc-last
    with ls .phase ≟ Receiving
  ... | no ph≢
    = no λ where (_ , LocalStep (TimerExpired ph≡ _) , refl) → ph≢ ph≡
  ... | yes ph≡
    with ¿ timedOut ls (s .currentTime) ¿
  ... | no ¬tm
    = no λ where (_ , LocalStep (TimerExpired _ tm) , refl) → ¬tm tm
  ... | yes tm
    = yes $ -, LocalStep (TimerExpired ph≡ tm) , refl
  Dec-ValidAction {x = AdvanceRoundQC qc}{s} .dec
    using ls  ← s .pls
    with ls .phase ≟ AdvancingRound
  ... | no ph≢
    = no λ where (_ , LocalStep (AdvanceRoundQC ph≡ _ _) , refl) → ph≢ ph≡
  ... | yes ph≡
    with qc ∙∈? ls .db
  ... | no qc∉
    = no λ where (_ , LocalStep (AdvanceRoundQC _ qc∈ _) , refl) → qc∉ qc∈
  ... | yes qc∈
    with ¿ qc ∙round ≥ ls .r-cur ¿
  ... | no r≱
    = no λ where (_ , LocalStep (AdvanceRoundQC _ _ r≥) , refl) → r≱ r≥
  ... | yes r≥
    = yes $ -, LocalStep (AdvanceRoundQC ph≡ qc∈ r≥) , refl
  Dec-ValidAction {x = AdvanceRoundTC tc}{s} .dec
    using ls  ← s .pls
    with ls .phase ≟ AdvancingRound
  ... | no ph≢
    = no λ where (_ , LocalStep (AdvanceRoundTC ph≡ _ _) , refl) → ph≢ ph≡
  ... | yes ph≡
    with tc ∙∈? ls .db
  ... | no tc∉
    = no λ where (_ , LocalStep (AdvanceRoundTC _ tc∈ _) , refl) → tc∉ tc∈
  ... | yes tc∈
    with ¿ tc ∙round ≥ ls .r-cur ¿
  ... | no r≱
    = no λ where (_ , LocalStep (AdvanceRoundTC _ _ r≥) , refl) → r≱ r≥
  ... | yes r≥
    = yes $ -, LocalStep (AdvanceRoundTC ph≡ tc∈ r≥) , refl
  Dec-ValidAction {x = AdvanceRoundNoOp}{s} .dec
    using ls  ← s .pls
    with ls .phase ≟ AdvancingRound
  ... | no ph≢
    = no λ where (_ , LocalStep (AdvanceRoundNoOp ph≡ _ _) , refl) → ph≢ ph≡
  ... | yes ph≡
    with ¿ AllQC (λ qc → qc ∙round < ls .r-cur) (ls .db) ¿
  ... | no qr≮
    = no λ where (_ , LocalStep (AdvanceRoundNoOp _ qr< _) , refl) → qr≮ qr<
  ... | yes qr<
    with ¿ AllTC (λ tc → tc ∙round < ls .r-cur) (ls .db) ¿
  ... | no tr≮
    = no λ where (_ , LocalStep (AdvanceRoundNoOp _ _ tr<) , refl) → tr≮ tr<
  ... | yes tr<
    = yes $ -, LocalStep (AdvanceRoundNoOp ph≡ qr< tr<) , refl
  Dec-ValidAction {x = Lock qc}{s} .dec
    using ls  ← s .pls
    with ls .phase ≟ Locking
  ... | no ph≢
    = no λ where (_ , LocalStep (Lock ph≡ _) , refl) → ph≢ ph≡
  ... | yes ph≡
    with ¿ qc -highest-qc-∈- ls .db ¿
  ... | no qc∉
    = no λ where (_ , LocalStep (Lock _ qc∈) , refl) → qc∉ qc∈
  ... | yes qc∈
    = yes $ -, LocalStep (Lock ph≡ qc∈) , refl
  Dec-ValidAction {x = Commit (b , ch)}{s} .dec
    using ls  ← s .pls
    with ls .phase ≟ Committing
  ... | no ph≢
    = no λ where (_ , LocalStep (Commit ph≡ _) , refl) → ph≢ ph≡
  ... | yes ph≡
    with ¿ b ∶ ch longer-final-∈ ls ¿
  ... | no ch∉
    = no λ where (_ , LocalStep (Commit _ ch∈) , refl) → ch∉ ch∈
  ... | yes ch∈
    = yes $ -, LocalStep (Commit ph≡ ch∈) , refl
  Dec-ValidAction {x = CommitNoOp}{s} .dec
    using ls  ← s .pls
    with ls .phase ≟ Committing
  ... | no ph≢
    = no λ where (_ , LocalStep (CommitNoOp ph≡ _) , refl) → ph≢ ph≡
  ... | yes ph≡
    with ¿ NoBlock (_longer-final-∈ ls) (ls .db) ¿
  ... | no ∃b
    = no λ where (_ , LocalStep (CommitNoOp _ ∄b) , refl) → ∃b ∄b
  ... | yes ∄b
    = yes $ -, LocalStep (CommitNoOp ph≡ ∄b) , refl
  Dec-ValidAction {x = VoteBlock b}{s} .dec
    using ls  ← s .pls
    using m   ← Vote $ signData p (b ∙blockId , b ∙round)
    using L′  ← nextLeader ls
    with ls .phase ≟ Voting
  ... | no ph≢
    = no λ where (_ , LocalStep (VoteBlock ph≡ _ _) , refl) → ph≢ ph≡
  ... | yes ph≡
    with b ∙∈? ls .db
  ... | no b∉
    = no λ where (_ , LocalStep (VoteBlock _ b∈ _) , refl) → b∉ b∈
  ... | yes b∈
    with ¿ ShouldVote ls b ¿
  ... | no ¬sv
    = no λ where (_ , LocalStep (VoteBlock _ _ sv) , refl) → ¬sv sv
  ... | yes sv
    = yes $ -, LocalStep (VoteBlock ph≡ b∈ sv) , refl
  Dec-ValidAction {x = VoteBlockNoOp}{s} .dec
    using ls  ← s .pls
    with ls .phase ≟ Voting
  ... | no ph≢
    = no λ where (_ , LocalStep (VoteBlockNoOp ph≡ _) , refl) → ph≢ ph≡
  ... | yes ph≡
    with ¿ NoBlock (ShouldVote ls) (ls .db) ¿
  ... | no ∃b
    = no λ where (_ , LocalStep (VoteBlockNoOp _ ∄b) , refl) → ∃b ∄b
  ... | yes ∄b
    = yes $ -, LocalStep (VoteBlockNoOp ph≡ ∄b) , refl
  Dec-ValidAction {x = Deliver m}{s} .dec
    = yes $ -, Deliver m , refl
  Dec-ValidAction {x = WaitUntil t}{s} .dec
    using ls ← s .pls
    with ¿ s .currentTime < t ¿
  ... | no t<
    = no λ where (_ , WaitUntil _ t≮ , refl) → t< t≮
                 (_ , LocalStep (InitTC x x₁) , ())
                 (_ , LocalStep (InitNoTC x x₁) , ())
                 (_ , LocalStep (ProposeBlock x x₁) , ())
                 (_ , LocalStep (ProposeBlockNoOp x x₁) , ())
                 (_ , LocalStep (RegisterProposal m∈ x x₁ x₂ x₃) , ())
                 (_ , LocalStep (RegisterVote m∈ x x₁ x₂ x₃ x₄) , ())
                 (_ , LocalStep (RegisterTimeout m∈ x x₁ x₂) , ())
                 (_ , LocalStep (RegisterTC m∈ x x₁ x₂) , ())
                 (_ , LocalStep (EnoughTimeouts x x₁ x₂ x₃) , ())
                 (_ , LocalStep (TimerExpired x x₁) , ())
                 (_ , LocalStep (AdvanceRoundQC x x₁ x₂) , ())
                 (_ , LocalStep (AdvanceRoundTC x x₁ x₂) , ())
                 (_ , LocalStep (AdvanceRoundNoOp x x₁ x₂) , ())
                 (_ , LocalStep (Lock x x₁) , ())
                 (_ , LocalStep (Commit x x₁) , ())
                 (_ , LocalStep (CommitNoOp x x₁) , ())
                 (_ , LocalStep (VoteBlock x x₁ x₂) , ())
                 (_ , LocalStep (VoteBlockNoOp x x₁) , ())
  ... | yes t≮
    = yes $ -, WaitUntil _ t≮ , refl

-- ** soundness & completeness (by construction)

⟦_⟧ : ValidAction α s → SliceState
⟦ (s′ , _) ⟧ = s′

ValidAction-sound : (va : ValidAction α s) → s —→ ⟦ va ⟧
ValidAction-sound (_ , s→ , _) = s→

ValidAction-complete : (st : s —→ s′) → ValidAction (getLabel st) s
ValidAction-complete s→ = -, s→ , refl
-- ** validity of traces

getLabels : (s′ —↠ s) → Actions
getLabels = λ where
  (_ ∎) → []
  (_ —→⟨ st ⟩ tr) → getLabel st ∷ getLabels tr

ValidTrace : Actions → SliceState → Type
ValidTrace αs s = ∃ λ s′ → ∃ λ (st : s —↠ s′) → getLabels st ≡ αs

⟦_⟧∗ : ValidTrace αs s → SliceState
⟦ s′ , _ ⟧∗ = s′

ValidTrace-sound : (vas : ValidTrace αs s) → s —↠ ⟦ vas ⟧∗
ValidTrace-sound (_ , s↠ , refl) = s↠

ValidTrace-complete : (st : s —↠ s′) → ValidTrace (getLabels st) s
ValidTrace-complete s↠ = -, s↠ , refl

private
  variable
    A : Type
    x y : A
    xs : List A

  record _≡∈_ (x∈ : x ∈ xs) (y∈ : y ∈ xs) : Type where
    constructor _⊢_
    field x≡  : x ≡ y
          x∈≈ : x∈ ≡ subst (_∈ _) (sym x≡) y∈

  index≡∈ : {x∈ : x ∈ xs} {y∈ : y ∈ xs} → x∈ ≡∈ y∈ → L.Any.index x∈ ≡ L.Any.index y∈
  index≡∈ (refl ⊢ refl) = refl

  index-injective : (x∈ x∈′ : x ∈ xs) → L.Any.index x∈ ≡ L.Any.index x∈′ → x∈ ≡ x∈′
  index-injective (here refl) (here refl) _ = refl
  index-injective (there x∈) (there x∈′) i≡ =
    cong there $ index-injective x∈ x∈′ (Fi.suc-injective i≡)

  index-injective≈ : (x∈ : x ∈ xs) (y∈ : y ∈ xs) → L.Any.index x∈ ≡ L.Any.index y∈ → x∈ ≡∈ y∈
  index-injective≈ (here refl) (here refl) _ = refl ⊢ refl
  index-injective≈ (there x∈) (there y∈) i≡
    with refl ⊢ x∈≈y∈ ← index-injective≈ x∈ y∈ (Fi.suc-injective i≡)
    = refl ⊢ cong there x∈≈y∈

  toℕ-injective : (x∈ x∈′ : x ∈ xs) → toℕ x∈ ≡ toℕ x∈′ → x∈ ≡ x∈′
  toℕ-injective x∈ x∈′ = index-injective x∈ x∈′ ∘ Fi.toℕ-injective

  toℕ-injective≈ : (x∈ : x ∈ xs) (y∈ : y ∈ xs) → toℕ x∈ ≡ toℕ y∈ → x∈ ≡∈ y∈
  toℕ-injective≈ x∈ y∈ = index-injective≈ x∈ y∈ ∘ Fi.toℕ-injective

private
  InjAction : ∀ {A : Type} → (A → Action) → Type
  InjAction {A = A} = Injective≡ {A = A} {B = Action}

  Deliver-inj : InjAction Deliver
  Deliver-inj refl = refl

  WaitUntil-inj : InjAction WaitUntil
  WaitUntil-inj refl = refl

  ProposeBlock-inj : InjAction ProposeBlock
  ProposeBlock-inj refl = refl

  AdvanceRoundQC-inj : InjAction AdvanceRoundQC
  AdvanceRoundQC-inj refl = refl

  AdvanceRoundTC-inj : InjAction AdvanceRoundTC
  AdvanceRoundTC-inj refl = refl

  Lock-inj : InjAction Lock
  Lock-inj refl = refl

  VoteBlock-inj : InjAction VoteBlock
  VoteBlock-inj refl = refl

  _＝_ = _≡_ {A = Action}

  Commit-inj : Commit (b , ch) ＝ Commit (b′ , ch′) → ch ≡ ch′
  Commit-inj refl = refl

  RegisterProposal-inj : RegisterProposal (n , sb) ＝ RegisterProposal (n′ , sb′) →
    (n ≡ n′) × (sb ≡ sb′)
  RegisterProposal-inj refl = refl , refl

  RegisterVote-inj : ∀ {p p′} → RegisterVote (n , r , p , b) ＝ RegisterVote (n′ , r′ , p′ , b′) →
    (n ≡ n′) × (r ≡ r′) × (p ≡ p′) × (b ≡ b′)
  RegisterVote-inj refl = refl , refl , refl , refl

  RegisterTimeout-inj : ∀ {tm′} → RegisterTimeout (n , tm) ＝ RegisterTimeout (n′ , tm′) →
    (n ≡ n′) × (tm ≡ tm′)
  RegisterTimeout-inj refl = refl , refl

  RegisterTC-inj : RegisterTC (n , tc) ＝ RegisterTC (n′ , tc′) →
    (n ≡ n′) × (tc ≡ tc′)
  RegisterTC-inj refl = refl , refl

vα≡ : (vα vα′ : ValidAction α s) → ⟦ vα ⟧ ≡ ⟦ vα′ ⟧
vα≡ {s = s} (_ , st , refl) (_ , st′ , α≡)
  with st | st′
... | LocalStep st | Deliver _ = ⊥-elim $ getLabel≢Deliver s st (sym α≡)
... | LocalStep st | WaitUntil _ _ = ⊥-elim $ getLabel≢WaitUntil s st (sym α≡)
... | Deliver _ | LocalStep st = ⊥-elim $ getLabel≢Deliver s st α≡
... | WaitUntil _ _ | LocalStep st = ⊥-elim $ getLabel≢WaitUntil s st α≡
... | Deliver m | Deliver m′
  rewrite Deliver-inj α≡
  = refl
... | WaitUntil t <t | WaitUntil t′ <t′
  rewrite WaitUntil-inj α≡
  = refl
... | LocalStep st | LocalStep st′
  with st | st′
... | InitTC _ refl | InitTC _ refl
  = refl
... | InitNoTC _ _ | InitNoTC _ _
  = refl
... | ProposeBlock _ _ | ProposeBlock _ _
  rewrite ProposeBlock-inj α≡
  = refl
... | ProposeBlockNoOp _ _ | ProposeBlockNoOp _ _
  = refl
... | RegisterProposal m∈ _ _ _ _ | RegisterProposal m∈′ _ _ _ _
  with n≡ , refl ← RegisterProposal-inj α≡
  with refl ⊢ refl ← toℕ-injective≈ m∈′ m∈ n≡
  = refl
... | RegisterVote m∈ _ _ _ _ _ | RegisterVote m∈′ _ _ _ _ _
  with n≡ , refl , refl , refl ← RegisterVote-inj α≡
  with refl ⊢ refl ← toℕ-injective≈ m∈′ m∈ n≡
  = refl
... | RegisterTimeout m∈ _ _ _ | RegisterTimeout m∈′ _ _ _
  with n≡ , refl ← RegisterTimeout-inj α≡
  with refl ⊢ refl ← toℕ-injective≈ m∈′ m∈ n≡
  = refl
... | RegisterTC m∈ _ _ _ | RegisterTC m∈′ _ _ _
  with n≡ , refl ← RegisterTC-inj α≡
  with refl ⊢ refl ← toℕ-injective≈ m∈′ m∈ n≡
  = refl
... | EnoughTimeouts _ _ _ _ | EnoughTimeouts _ _ _ _
  = refl
... | TimerExpired _ _ | TimerExpired _ _
  = refl
... | AdvanceRoundQC _ _ _ | AdvanceRoundQC _ _ _
  rewrite AdvanceRoundQC-inj α≡
  = refl
... | AdvanceRoundTC _ _ _ | AdvanceRoundTC _ _ _
  rewrite AdvanceRoundTC-inj α≡
  = refl
... | AdvanceRoundNoOp _ _ _ | AdvanceRoundNoOp _ _ _
  = refl
... | Lock _ _ | Lock _ _
  rewrite Lock-inj α≡
  = refl
... | Commit _ _ | Commit _ _
  rewrite Commit-inj α≡
  = refl
... | CommitNoOp _ _ | CommitNoOp _ _
  = refl
... | VoteBlock _ _ _ | VoteBlock _ _ _
  rewrite VoteBlock-inj α≡
  = refl
... | VoteBlockNoOp _ _ | VoteBlockNoOp _ _
  = refl

vαs⇒ : (vα vα′ : ValidAction α s) →
  ValidTrace αs ⟦ vα ⟧ → ValidTrace αs ⟦ vα′ ⟧
vαs⇒ vα vα′ = subst (ValidTrace _) (vα≡ vα vα′)

private
  getLabel≡ : (vα : ValidAction α s) → getLabel (ValidAction-sound vα) ≡ α
  getLabel≡ (_ , _ , α≡) = α≡

  getLabels≡ : (vαs : ValidTrace αs s) → getLabels (ValidTrace-sound vαs) ≡ αs
  getLabels≡ (_ , _ , refl) = refl

instance
  Dec-ValidTrace : ValidTrace ⁇²
  Dec-ValidTrace {x = tr}{s} .dec with tr
  ... | [] = yes (-, (_ ∎) , refl)
  ... | α ∷ αs
    with ¿ ValidAction α s ¿
  ... | no ¬vα = no λ where
    (_ , (_ —→⟨ st ⟩ tr) , refl) → ¬vα (-, st , refl)
  ... | yes vα
    with ¿ ValidTrace αs ⟦ vα ⟧ ¿
  ... | no ¬vαs = no λ where
    (_ , (_ —→⟨ st ⟩ tr) , refl) →
      ¬vαs $ vαs⇒ (-, st , refl) vα (ValidTrace-complete tr)
  ... | yes vαs
    = yes (-, (_ —→⟨ ValidAction-sound vα ⟩ ValidTrace-sound vαs)
            , cong₂ _∷_ (getLabel≡ vα) (getLabels≡ vαs))
