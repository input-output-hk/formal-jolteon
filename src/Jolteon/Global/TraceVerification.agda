{-# OPTIONS --safe #-}

open import Jolteon.Base
open import Jolteon.Assumptions

module Jolteon.Global.TraceVerification (⋯ : _) (open Assumptions ⋯) where

open import Prelude
open import Prelude.Result

open import Jolteon.Decidability ⋯
open import Jolteon.Block ⋯
open import Jolteon.Message ⋯

open import Jolteon.Local.State ⋯
open import Jolteon.Local.Step ⋯

open import Jolteon.Global.State ⋯
open import Jolteon.Global.Step ⋯
open import Jolteon.Global.Trace ⋯

open import Jolteon.Global.TraceVerification.LocalStep ⋯

-- Test traces ---

data Event : Type where
  Deliver   : (p : Pid) (msg : Message) → Event
  LocalStep : (p : Pid) (lbl : StepLabel) → Event

TestTrace = List (Time × Event)

private variable
  t₀         : Time
  e e₁ e₂    : Event
  es es′     : TestTrace
  ls₁        : LocalState
  s₁ s₂      : GlobalState
  lbl        : StepLabel
  lbls lbls′ : List StepLabel

-- Helpers ---

record Dict (A : Type) : Type where
  constructor dict
  field
    ⦃ i ⦄ : A

checkHonest : (p : Pid) → Result (Dishonest p) (Dict (Honest p))
checkHonest p = do
  h ← ¿ Honest p ¿ᴿ
  Ok (dict ⦃ h ⦄)

-- Note: we pick the first matching message, which is safe since the buffer is sorted.
findMessage : (p : Pid) (m : Message) (buf : TPMessages)
            → Result (∀ t₀ → (t₀ , p , m) ∉ buf)
                     (∃[ t ] (t , p , m) ∈ buf)
findMessage p m [] = Err λ _ ()
findMessage p m ((t , p₁ , m₁) ∷ buf) with (p , m) ≟ (p₁ , m₁)
... | yes refl = return (t , here refl)
... | no neq   = do
  t , tpm∈ ← findMessage p m buf `mapErr` λ where
    tpm∉ t₀ (here refl)  → neq refl
    tpm∉ t₀ (there tpm∈) → tpm∉ t₀ tpm∈
  return (t , there tpm∈)

-- Valid traces ---

infix 0 _≈_
data _≈_ : TestTrace → (s —↠ s′) → Type where

  LocalStep
    : ∀ (let now = currentTime s)
        ⦃ _ : Honest p ⦄
        {tr : broadcast now menv (s ＠ p ≔ ls₁) —↠ s′}
      → (step : p ⦂ now ⊢ s ＠ p — menv —→ ls₁)
      → stepLabel step ≡ lbl
      → es ≈ tr
      → (now , LocalStep p lbl) ∷ es ≈ s —→⟨ LocalStep step ⟩ tr

  Deliver
    : ∀ (let now = currentTime s)
        (tpm∈ : (t , p , m) ∈ s. networkBuffer)
        {tr : _ —↠ s′}
      → es ≈ tr
      → (now , Deliver p m) ∷ es ≈ s —→⟨ Deliver tpm∈ ⟩ tr

  WaitUntil
    : ∀ (let now = currentTime s)
        {now<t} {inTime}
        {tr : _ —↠ s′}
      → es ≈ tr
      → es ≈ s —→⟨ WaitUntil t inTime now<t ⟩ tr

  Done : [] ≈ s ∎

≈-trans : {tr : s —↠ s₁} {tr′ : s₁ —↠ s₂} → [] ≈ tr → es ≈ tr′ → es ≈ —↠-trans tr tr′
≈-trans (WaitUntil p) q = WaitUntil (≈-trans p q)
≈-trans Done          q = q

data ValidTrace (es : TestTrace) (s : GlobalState) : Type where
  Valid : (tr : s —↠ s′) → es ≈ tr → ValidTrace es s

-- Stepping time ---

data Err-stepTime (t : Time) (s : GlobalState) : Type where

  E-Late
    : ¬ All (λ (t′ , _ , _) → t ≤ t′ + Δ) (s .networkBuffer)
    → Err-stepTime t s

  E-TimeTravel
    : ¬ (currentTime s ≤ t)
    → Err-stepTime t s

stepTime : (t : Time) (s : GlobalState)
         → Result (Err-stepTime t s)
                  (Σ (s —↠ record s { currentTime = t }) λ tr → [] ≈ tr)
stepTime t s with t ≟ s .currentTime
... | yes refl = return ((s ∎) , Done)
... | no t≠now = do
  noLate ← ¿ All (λ (t′ , _ , _) → t ≤ t′ + Δ) (s .networkBuffer) ¿ᴿ: E-Late
  now<t  ← ¿ currentTime s < t ¿ᴿ: λ now≮t → E-TimeTravel (t≠now ∘ Nat.≤-antisym (Nat.≮⇒≥ now≮t))
  return ((s —→⟨ WaitUntil t noLate now<t ⟩ _ ∎) , WaitUntil Done)

-- Global trace verification ---

private variable
  ps : List Pid

data Err-verifyTrace : (es : TestTrace)
                     → (s : GlobalState)
                     → Type where
  E-LocalStepOk
    : Err-verifyTrace es s₁
    → Err-verifyTrace ((t , LocalStep p lbl) ∷ es) s

  E-DeliverOk
    : Err-verifyTrace es s₁
    → Err-verifyTrace ((t , Deliver p m) ∷ es) s

  E-Deliver
    : (∀ t₀ → (t₀ , p , m) ∉ s .networkBuffer)
    → Err-verifyTrace ((t , Deliver p m) ∷ es) s

  E-LocalStep
    : ⦃ _ : Honest p ⦄
    → (lbl : StepLabel)
    → Err-verifyLocal t p (s ＠ p) lbl
    → Err-verifyTrace ((t , LocalStep p lbl) ∷ es) s

  E-Dishonest
    : Dishonest p
    → Err-verifyTrace ((t , LocalStep p lbl) ∷ es) s

  E-StepTime
    : Err-stepTime t s
    → Err-verifyTrace ((t , e) ∷ es) s

verifyTrace : ∀ (es : TestTrace)
              → (s : GlobalState)
              → Result (Err-verifyTrace es s)
                       (ValidTrace es s)
verifyTrace [] s = return (Valid (s ∎) Done)
verifyTrace ((t , Deliver p m) ∷ es) s = do
  tr₁ , prf₁   ← stepTime t s                       `mapErr` E-StepTime
  _ , tpm∈     ← findMessage p m (s .networkBuffer) `mapErr` E-Deliver
  Valid tr prf ← verifyTrace es _                   `mapErr` E-DeliverOk
  let trace = —↠-trans tr₁ (_ —→⟨ Deliver tpm∈ ⟩ tr)
  return (Valid trace (≈-trans prf₁ (Deliver tpm∈ prf)))
verifyTrace ((t , LocalStep p lbl) ∷ es) s = do
  tr₁ , prf₁            ← stepTime t s                 `mapErr` E-StepTime
  dict                  ← checkHonest p                `mapErr` E-Dishonest
  menv , s₁ , step , eq ← verifyLocal t p lbl (s ＠ p) `mapErr` E-LocalStep lbl
  Valid tr prf          ← verifyTrace es _             `mapErr` E-LocalStepOk
  let trace = —↠-trans tr₁ (_ —→⟨ LocalStep step ⟩ tr)
  return (Valid trace (≈-trans prf₁ (LocalStep step eq prf)))

-- Formal traces to test trace ---

pmDelivered : Time → Pid × Message → Time × Event
pmDelivered t (p , m) = t , Deliver p m

eraseTrace : s —↠ s′ → TestTrace
eraseTrace (_ ∎) = []
eraseTrace (s —→⟨ LocalStep {p = p} step        ⟩ tr) = (s .currentTime , LocalStep p (stepLabel step)) ∷ eraseTrace tr
eraseTrace (_ —→⟨ DishonestLocalStep x x₁       ⟩ tr) = eraseTrace tr   -- TODO: dishonest traces
eraseTrace (s —→⟨ Deliver {tpm = (_ , p , m)} _ ⟩ tr) = (s .currentTime , Deliver p m) ∷ eraseTrace tr
eraseTrace (_ —→⟨ WaitUntil _ _ _               ⟩ tr) = eraseTrace tr

roundTripTrace : (tr : s —↠ s′) → Result ⊤ (ValidTrace (eraseTrace tr) s)
roundTripTrace {s} tr = verifyTrace (eraseTrace tr) s `mapErr` λ _ → _
