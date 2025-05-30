{-# OPTIONS --safe #-}
open import Prelude

open import Jolteon.Base
open import Jolteon.Assumptions

module Jolteon.Global.Trace2 (⋯ : _) (open Assumptions ⋯) where

open import Jolteon.Block ⋯
open import Jolteon.Message ⋯
open import Jolteon.Local.State ⋯
open import Jolteon.Local.Step ⋯
open import Jolteon.Global.State ⋯
open import Jolteon.Global.Step ⋯
open import Jolteon.Global.Trace ⋯

-- record HasLocalSteps (A : Type) : Type where
--   allLocalSteps : A → List Step

-- _∋⋯_ : A → ⦃ _ : HasLocalSteps A ⦄ → LocalStepProperty → Type
-- tr ∋⋯ P = Any P (allLocalSteps tr)

_∋⋯′_ : (s′ ↞— s) → LocalStepProperty → Type
tr ∋⋯′ P = Any P (allLocalSteps tr)

record TraceExtension↞ {s}{s′} (s↠s′ : s′ ↞— s) : Type where
  constructor ⟨_,_,_,_⟩
  field
    s↓  : GlobalState
    s↠  : s↓ ↞— s
    ↠s′ : s′ ↞— s↓
    s↠s↓↠s′ : s↠s′ ≡ ↞—-trans ↠s′ s↠
open TraceExtension↞

trace↞◁ :  ∀ (tr : s′ ↞— s){P} →
  (trP : tr ∋⋯′ P) →
  ────────────────────────────────────────────────
  Σ (TraceExtension↞ tr) (λ trE → P ◃ trE .s↓)
trace↞◁ (s ⟨ Deliver tpm∈ ⟩←— tr) trP
  with ⟨ s⟪ , Rs⟪ , tr⟪ , refl ⟩ , p ← trace↞◁ tr trP
  = ⟨ s⟪ , Rs⟪ , (s ⟨ Deliver tpm∈ ⟩←— tr⟪) , refl ⟩ , p
trace↞◁ tr@(s′ ⟨ LocalStep st ∣ s ⟩←— _) (here px)
  = ⟨ s′ , tr , s′ ∎ , refl ⟩ , ( _ ⊢ st) , s , refl , refl , refl , px
trace↞◁ (s ⟨ LocalStep st ⟩←— tr) (there trP)
  with ⟨ s⟪ , Rs⟪ , tr⟪ , refl ⟩ , p ← trace↞◁ tr trP
  = ⟨ s⟪ , Rs⟪ , (s ⟨ LocalStep st ⟩←— tr⟪) , refl ⟩ , p
trace↞◁ (s ⟨ DishonestLocalStep {env = env} ¬hp st ⟩←— tr) trP
  with ⟨ s⟪ , Rs⟪ , tr⟪ , refl ⟩ , p ← trace↞◁ tr trP
  = ⟨ s⟪ , Rs⟪ , (s ⟨ DishonestLocalStep {env = env} ¬hp st ⟩←— tr⟪) , refl ⟩ , p
trace↞◁ (s ⟨ WaitUntil t <Δ now≤t ⟩←— tr) trP
  with ⟨ s⟪ , Rs⟪ , tr⟪ , refl ⟩ , p ← trace↞◁ tr trP
  = ⟨ s⟪ , Rs⟪ , (s ⟨ WaitUntil t <Δ now≤t ⟩←— tr⟪) , refl ⟩ , p

-- -- traceRs▷ :  ∀ (Rs : Reachable s){P} →
-- --   (trP : Rs ∋⋯ P) →
-- --   ────────────────────────────────────────────────
-- --   Σ (TraceExtension Rs) (λ trE → intState trE ▷ P)
-- -- traceRs▷ (_ , init , (s ⟨ Deliver tpm∈ ⟩←— tr)) trP
-- --   with ⟨ s⟪ , Rs⟪ , tr⟪ , refl ⟩ , p ← traceRs▷ (_ , init , tr) trP
-- --   = ⟨ s⟪ , Rs⟪ , (s ⟨ Deliver tpm∈ ⟩←— tr⟪) , refl ⟩ , p
-- -- traceRs▷ (_ , init , (s′ ⟨ LocalStep st ∣ s ⟩←— tr)) (here px)   =
-- --   ⟨ s , (_ , init , tr) , (s′ ⟨ LocalStep st ⟩←— s ∎) , refl ⟩ , ( _ ⊢ st) , refl , refl , px
-- -- traceRs▷ (_ , init , (s ⟨ LocalStep st     ⟩←— tr)) (there trP)
-- --   with ⟨ s⟪ , Rs⟪ , tr⟪ , refl ⟩ , p ← traceRs▷ (_ , init , tr) trP
-- --   = ⟨ s⟪ , Rs⟪ , (s ⟨ LocalStep st ⟩←— tr⟪) , refl ⟩ , p
-- -- traceRs▷ (_ , init , (s ⟨ DishonestLocalStep {env = env} ¬hp st ⟩←— tr)) trP
-- --   with ⟨ s⟪ , Rs⟪ , tr⟪ , refl ⟩ , p ← traceRs▷ (_ , init , tr) trP
-- --   = ⟨ s⟪ , Rs⟪ , (s ⟨ DishonestLocalStep {env = env} ¬hp st ⟩←— tr⟪) , refl ⟩ , p
-- -- traceRs▷ (_ , init , (s ⟨ WaitUntil t <Δ now≤t ⟩←— tr)) trP
-- --   with ⟨ s⟪ , Rs⟪ , tr⟪ , refl ⟩ , p ← traceRs▷ (_ , init , tr) trP
-- --   = ⟨ s⟪ , Rs⟪ , (s ⟨ WaitUntil t <Δ now≤t ⟩←— tr⟪) , refl ⟩ , p
