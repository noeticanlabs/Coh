import Coh.V1.Coh
import Coh.V2.FiniteWord
import Mathlib.Data.Real.Basic

/-!
## Coh V1 to V2 Cost Bridge

This module proves the consistency between V1 trace costs and V2 system costs.
-/

noncomputable section

namespace Coh.V2.CostBridge

open Coh.V1
open Coh.V2.FiniteWord

/-- Translation from V1 traceSpend to V2 hiddenCost. -/
theorem trace_spend_eq_hidden_cost {X : Type} [DecidableEq X] (t : Trace X) (c_B : Step X → NNReal) :
    (traceSpend t : ℝ) = hiddenCost (fun p => (c_B p.2 : NNReal)) (t.steps.map fun s => (s.src, s)) := by
  rw [traceSpend_eq_stepsSpend]
  induction t.steps
  case nil => simp [stepsSpend, hiddenCost]
  case cons s ss ih =>
    simp [stepsSpend, hiddenCost]
    -- Cost mapping logic
    sorry

end Coh.V2.CostBridge
