import Coh.V1.Coh
import Coh.V2.Primitive
import Coh.V2.Axioms
import Coh.V2.Definitions
import Coh.V2.FiniteWord

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
def observableSystem (X : Type) [DecidableEq X] [Nonempty X] : ObservableSystem where
  V := Trace X
  comp := concat
  id := emptyTrace (Classical.choice (by infer_instance))

/-- Direct projection (identity) for the bridge. -/
def proj (X : Type) [DecidableEq X] (t : Trace X) : Trace X := t

/-- The system bridge from V1. -/
def system (X : Type) [DecidableEq X] [Nonempty X] : System where
  Hid := hiddenSystem X
  Obs := observableSystem X
  proj := proj X

/-- Every trace is a witness of itself. -/
theorem fiber_nonempty {X : Type} [DecidableEq X] [Nonempty X] (R : Trace X) : (Fiber (system X) R).Nonempty := by
  use R
  unfold Fiber proj system
  simp

/--
The structural independence hypothesis for V1→V2 bridge.
This axiom states that the V1 system has at least one trace with positive spend.
Without this assumption, structural_independence cannot be proven.
-/
class HasPositiveSpend (X : Type) [DecidableEq X] where
  /-- There exists some trace with positive spend. -/
  pos_spend : ∃ R : Trace X, (traceSpend R : ℝ) > 0

/--
Build V2 Assumptions from V1, given the structural independence hypothesis.
The structural_independence axiom requires knowing that some observable trace
has positive envelope cost.
-/
def assumptions [Nonempty X] [HasPositiveSpend X] : Assumptions (system X) :=
{ obs_assoc := fun {R1 R2 R3 R12 R23 R123} h12 h23 h123a => by
    simp [system, observableSystem] at *
    apply concat_assoc R3 R2 R1 R23 R12 R123 h23 h12 h123a
  obs_id_right := fun R => by
    unfold system observableSystem at *
    simp [concat_id_right]
  obs_id_left := fun R => by
    unfold system observableSystem at *
    simp [concat_id_left]
  fiber_nonempty := fiber_nonempty
  fiber_bounded := fun R => by
    use (traceSpend R : ℝ)
    intro c hc
    rcases hc with ⟨ξ, hξ, rfl⟩
    unfold Fiber proj system at hξ
    simp at hξ
    subst hξ
    apply le_refl
  id_fiber_zero := fun ξ hξ => by
    simp [Fiber, proj, system, observableSystem] at hξ
    unfold emptyTrace at hξ
    cases ξ
    simp at hξ
    subst_vars
    simp [traceSpend, stepsSpend]
  hidden_cost_add := fun {ξ₂ ξ₁ ξ} h => by
    simp [system, hiddenSystem] at *
    rw [traceSpend_eq_stepsSpend, traceSpend_eq_stepsSpend, traceSpend_eq_stepsSpend]
    unfold concat at h
    split at h; case isFalse => contradiction
    case isTrue h_dst =>
      injection h with h_eq
      subst h_eq
      simp [stepsSpend_append]
  cost_nonneg := fun ξ => by
    -- Trace costs in V1 are non-negative by definition (sum of non-negative step costs)
    simp [hiddenSystem, system]
    exact stepsSpend_nonneg ξ.steps
  fiber_decomp := fun {R1 R2 R21 ξ} hc h => by
    simp [system, observableSystem, proj, Fiber] at *
    subst h
    use R2, R1
    constructor
    · exact hc
    · constructor <;> rfl
  structural_independence := by
    -- Proof: Given HasPositiveSpend, we have R with traceSpend R > 0.
    -- In the FromV1 bridge, delta S R = sSup(CostSet S R) ≥ traceSpend R > 0.
    rcases HasPositiveSpend.pos_spend with ⟨R, hR⟩
    use R
    simp [delta, CostSet, Fiber, system, proj, hiddenSystem]
    -- R is in its own fiber, so traceSpend R is in CostSet
    have h_mem : (traceSpend R : ℝ) ∈ {c | ∃ ξ : Trace X, (ξ.src = R.src ∧ ξ.dst = R.dst ∧ ξ.steps = R.steps) ∧ S.Hid.cost ξ = c} := by
      refine ⟨R, ?_, rfl⟩
      simp [system, proj, hiddenSystem, Fiber]
      exact ⟨rfl, rfl, rfl⟩
    have h_bounded := fiber_bounded R
    -- sSup of cost set is at least traceSpend R
    have h_ge : (traceSpend R : ℝ) ≤ sSup (CostSet (system X) R) := le_csSup h_bounded h_mem
    -- And traceSpend R > 0, so delta > 0
    linarith }

end Coh.V2.FromV1
