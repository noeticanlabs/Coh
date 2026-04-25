import Coh.V1.Coh
import Coh.V2.FiniteWord
import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.Order.Field.Rat
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
    (t : Trace X) (C : ℚ) (h_bound : ∀ (s : Step X), s.costSpend ≤ C) :
    (traceSpend t : ℚ) ≤ (t.steps.length : ℚ) * C := by
  rw [traceSpend_eq_stepsSpend]
  induction t.steps
  case nil => simp [stepsSpend]
  case cons s ss ih =>
    simp [stepsSpend]
    have h_max : s.costSpend ≤ C := h_bound s
    have h_total := add_le_add h_max ih
    linarith

/-- Lemma: A valid chain can be split at any point in its step list. -/
theorem is_chain_split {X : Type} {s e : X} {L1 L2 : List (Step X)} :
    is_chain s e (L1 ++ L2) → ∃ m, is_chain s m L1 ∧ is_chain m e L2 := by
  induction L1 generalizing s
  case nil =>
    intro h
    simp [is_chain] at h
    use s
    simp [is_chain, h]
  case cons head tail ih =>
    intro h
    simp [is_chain] at h
    rcases h with ⟨h_src, h_tail⟩
    rcases ih h_tail with ⟨m, h_tail1, h_tail2⟩
    use m
    simp [is_chain, h_src, h_tail1, h_tail2]

end Coh.V2.BridgeLemmas
