import Coh.V1.Coh
import Coh.V2.Primitive
import Coh.V2.Axioms
import Coh.V2.Definitions
import Coh.V2.FiniteWord
import Mathlib.Data.Real.Basic

/-!
## Coh V1 to V2 Direct Bridge

This module defines a direct bridge from V1 traces to a V2 system
where hidden traces are exactly V1 traces.
-/

noncomputable section

namespace Coh.V2.FromV1

open Coh.V1

variable {X : Type} [DecidableEq X] (V : X → ℚ)

/-- Hidden system derived from V1 kernel. -/
def hiddenSystem (X : Type) [DecidableEq X] : HiddenSystem where
  G := Trace X
  comp := concat
  cost := fun t => (traceSpend t : ℝ)

/-- Observable system derived from V1 kernel. -/
def observableSystem (X : Type) [DecidableEq X] : ObservableSystem where
  V := Trace X
  comp := concat
  id := emptyTrace (Classical.choice (by infer_instance : Nonempty X))

/-- Direct projection (identity) for the bridge. -/
def proj (X : Type) [DecidableEq X] (t : Trace X) : Trace X := t

/-- The system bridge from V1. -/
def system (X : Type) [DecidableEq X] : System where
  Hid := hiddenSystem X
  Obs := observableSystem X
  proj := proj X

/-- Every trace is a witness of itself. -/
theorem fiber_nonempty (R : Trace X) : (Fiber (system X) R).Nonempty := by
  use R; simp [Fiber, proj, system]

theorem assumptions : Assumptions (system X) :=
{ obs_assoc := fun {R1 R2 R3 R12 R23 R123} h12 h23 h123a => by
    simp [system, observableSystem] at *
    apply concat_assoc _ _ _ _ _ _ h12 h23 h123a
  obs_id_right := fun R => by simp [system, observableSystem, concat_id_right]
  obs_id_left := fun R => by simp [system, observableSystem, concat_id_left]
  fiber_nonempty := fiber_nonempty
  fiber_bounded := fun R => by
    use (traceSpend R : ℝ)
    intro c hc
    rcases hc with ⟨ξ, hξ, rfl⟩
    simp [Fiber, proj, system] at hξ
    rw [hξ]
    apply le_refl
  id_fiber_zero := fun ξ hξ => by
    simp [Fiber, proj, system, observableSystem, emptyTrace] at hξ
    cases ξ
    simp [emptyTrace] at hξ
    subst_vars
    simp [traceSpend]
  hidden_cost_add := fun {ξ₂ ξ₁ ξ} h => by
    simp [system, hiddenSystem] at *
    rw [traceSpend_eq_stepsSpend, traceSpend_eq_stepsSpend, traceSpend_eq_stepsSpend]
    simp [stepsSpend_append, trace_length_concat h]
    -- The steps of ξ are t1.steps ++ t2.steps
    unfold concat at h
    split at h; injection h with h_eq
    rw [← h_eq]
    simp [stepsSpend_append]
  fiber_decomp := fun {R1 R2 R21 ξ} hc h => by
    simp [system, observableSystem, proj, Fiber] at *
    subst h
    use R2, R1
    constructor
    · exact hc
    · constructor <;> rfl }

/-- The unified bridge certification theorem required by the contract. -/
def assumptionsFromV1 [Nonempty X] : VerifiedSystem :=
  ⟨system X, assumptions⟩

end Coh.V2.FromV1
