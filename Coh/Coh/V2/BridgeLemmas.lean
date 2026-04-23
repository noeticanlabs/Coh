import Coh.V1.Coh
import Mathlib.Tactic.Basic

namespace Coh.V2

open Coh.V1

/-- Zero cost for identity traces. -/
theorem traceSpend_empty {X : Type} (x : X) : 
    traceSpend (emptyTrace x) = 0 := by
  rw [traceSpend_eq_stepsSpend]
  simp [emptyTrace, stepsSpend]

/-- Zero defect for identity traces. -/
theorem traceDefect_empty {X : Type} (x : X) : 
    traceDefect (emptyTrace x) = 0 := by
  rw [traceDefect_eq_stepsDefect]
  simp [emptyTrace, stepsDefect]

/-- Cost functions are independent of the trace endpoints, only depending on the steps. -/
theorem traceSpend_indep {X : Type} (s1 d1 s2 d2 : X) (steps : List (Step X)) (c1 : is_chain s1 d1 steps) (c2 : is_chain s2 d2 steps) :
    traceSpend ⟨s1, d1, steps, c1⟩ = traceSpend ⟨s2, d2, steps, c2⟩ := by
  rw [traceSpend_eq_stepsSpend, traceSpend_eq_stepsSpend]

theorem traceDefect_indep {X : Type} (s1 d1 s2 d2 : X) (steps : List (Step X)) (c1 : is_chain s1 d1 steps) (c2 : is_chain s2 d2 steps) :
    traceDefect ⟨s1, d1, steps, c1⟩ = traceDefect ⟨s2, d2, steps, c2⟩ := by
  rw [traceDefect_eq_stepsDefect, traceDefect_eq_stepsDefect]

/-- Trace spend is exactly additive under concatenation. -/
theorem traceSpend_concat {X : Type} [DecidableEq X] (t₁ t₂ t₁₂ : Trace X) 
    (hcomp : concat t₁ t₂ = some t₁₂) :
    traceSpend t₁₂ = traceSpend t₁ + traceSpend t₂ := by
  unfold concat at hcomp
  split at hcomp; case isFalse => contradiction
  case isTrue h =>
    injection hcomp with h_eq
    rw [traceSpend_eq_stepsSpend, traceSpend_eq_stepsSpend, traceSpend_eq_stepsSpend]
    rw [← h_eq]; simp
    apply stepsSpend_append

/-- Trace defect is exactly additive under concatenation. -/
theorem traceDefect_concat {X : Type} [DecidableEq X] (t₁ t₂ t₁₂ : Trace X) 
    (hcomp : concat t₁ t₂ = some t₁₂) :
    traceDefect t₁₂ = traceDefect t₁ + traceDefect t₂ := by
  unfold concat at hcomp
  split at hcomp; case isFalse => contradiction
  case isTrue h =>
    injection hcomp with h_eq
    rw [traceDefect_eq_stepsDefect, traceDefect_eq_stepsDefect, traceDefect_eq_stepsDefect]
    rw [← h_eq]; simp
    apply stepsDefect_append

end Coh.V2
