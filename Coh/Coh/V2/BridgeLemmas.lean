import Coh.V1.Coh
import Coh.V2.FiniteWord
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
## Coh V1 to V2 Bridge Lemmas

This module provides the analytical lemmas required to bridge the V1 trace kernel
with the V2 axiomatic categorical model.
-/

noncomputable section

namespace Coh.V2.BridgeLemmas

open Coh.V1
open Coh.V2.FiniteWord

/-- 
Lemma: The cost of a V1 trace is bounded by the V2 c_max.
This bridges the concrete V1 cost definition with the V2 analytical bounds.
-/
theorem trace_cost_bounded {X : Type} [Fintype X] [DecidableEq X] 
    (t : Trace X) (c_B : Step X → NNReal) :
    (traceSpend t : ℝ) ≤ (t.steps.length : ℝ) * (c_max (fun s => (c_B s : NNReal)) : ℝ) := by
  rw [traceSpend_eq_stepsSpend]
  induction t.steps
  case nil => simp [stepsSpend]
  case cons s ss ih =>
    simp [stepsSpend]
    have h_max : (c_B s : ℝ) ≤ (c_max (fun s => (c_B s : NNReal)) : ℝ) := by
      apply NNReal.coe_le_coe.mpr
      apply Finset.le_max'
      apply Finset.mem_image_of_mem
      apply Finset.mem_univ
    linarith

end Coh.V2.BridgeLemmas
