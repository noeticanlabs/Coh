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
Lemma: The cost of a V1 trace is bounded by a constant C.
This bridges the concrete V1 cost definition with the V2 analytical bounds.
-/
theorem trace_cost_bounded {X : Type} [DecidableEq X] 
    (t : Trace X) (c_B : Step X → NNReal) (C : NNReal) (h_bound : ∀ s, c_B s ≤ C) :
    (traceSpend t : ℝ) ≤ (t.steps.length : ℝ) * (C : ℝ) := by
  rw [traceSpend_eq_stepsSpend]
  induction t.steps
  case nil => simp [stepsSpend]
  case cons s ss ih =>
    simp [stepsSpend]
    have h_max : (c_B s : ℝ) ≤ (C : ℝ) := NNReal.coe_le_coe.mpr (h_bound s)
    have h_total := add_le_add h_max ih
    refine h_total.trans ?_
    simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm]

end Coh.V2.BridgeLemmas
