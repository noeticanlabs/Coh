import Coh.V2.Analytic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
## Coh V2 Geometry Layer

This module formalizes the state-to-state quasi-metric distance $d(x, y)$.
It proves that this distance satisfies the non-negativity, identity, and 
triangle inequality axioms, grounding the Coh framework in metric geometry.
-/

namespace Coh.V2

noncomputable section

/-- 
A TransitionSystem extends a System with a state space X and a mapping
that identifies the source and target states of each observable trace.
-/
structure TransitionSystem (S : System) (X : Type _) where
  src : S.Obs.V → X
  dst : S.Obs.V → X
  id_state : ∀ x : X, src S.Obs.id = x ∧ dst S.Obs.id = x
  comp_src : ∀ {R₁ R₂ R₂₁}, S.Obs.comp R₂ R₁ = some R₂₁ → src R₂₁ = src R₁
  comp_dst : ∀ {R₁ R₂ R₂₁}, S.Obs.comp R₂ R₁ = some R₂₁ → dst R₂₁ = dst R₂
  comp_mid : ∀ {R₁ R₂ R₂₁}, S.Obs.comp R₂ R₁ = some R₂₁ → dst R₁ = src R₂
  comp_defined : ∀ {R₁ R₂}, dst R₁ = src R₂ → ∃ R₂₁, S.Obs.comp R₂ R₁ = some R₂₁

/-- The set of observable traces between two states. -/
def Traces (S : System) {X : Type _} (T : TransitionSystem S X) (x y : X) : Set S.Obs.V :=
  { R | T.src R = x ∧ T.dst R = y }

/-- 
The state-to-state distance d(x, y) is the infimum of the defect envelope
over all observable traces between x and y.
-/
def d {S : System} {X : Type _} (A : Assumptions S) (T : TransitionSystem S X) (x y : X) : ℝ :=
  sInf (delta S '' Traces S T x y)

/-- The distance to self is zero. -/
theorem d_id {S : System} {X : Type _} (A : Assumptions S) (T : TransitionSystem S X) (x : X) :
    d A T x x = 0 := by
  unfold d
  have h_id : S.Obs.id ∈ Traces S T x x := by
    simp [Traces, T.id_state]
  have h_delta_id : delta S S.Obs.id = 0 := delta_id A
  have h_zero_in : (0 : ℝ) ∈ delta S '' Traces S T x x := by
    use S.Obs.id
    simp [h_id, h_delta_id]
  apply le_antisymm
  · apply csInf_le
    · use 0
      intro r hr
      rcases hr with ⟨R, _, rfl⟩
      exact delta_nonneg A R
    · exact h_zero_in
  · apply le_csInf
    · use S.Obs.id, h_id, h_delta_id
    · intro r hr
      rcases hr with ⟨R, _, rfl⟩
      exact delta_nonneg A R

/-- Distance is non-negative for reachable states. -/
theorem d_nonneg {S : System} {X : Type _} (A : Assumptions S) (T : TransitionSystem S X) (x y : X) 
    (h_reachable : (Traces S T x y).Nonempty) :
    0 ≤ d A T x y := by
  unfold d
  have h_img_nonempty : (delta S '' Traces S T x y).Nonempty := by
    rcases h_reachable with ⟨R, hR⟩
    use delta S R, R, hR, rfl
  apply le_csInf h_img_nonempty
  intro r hr
  rcases hr with ⟨R, _, rfl⟩
  exact delta_nonneg A R

/-- 
The triangle inequality for the state-to-state distance.
d(x, z) ≤ d(x, y) + d(y, z)
-/
theorem d_triangle {S : System} (A : SegmentableAssumptions S) {X : Type _} 
    (T : TransitionSystem S X) (x y z : X) 
    (h_xy : (Traces S T x y).Nonempty) (h_yz : (Traces S T y z).Nonempty) :
    d A.toAssumptions T x z ≤ d A.toAssumptions T x y + d A.toAssumptions T y z := by
  -- For any r1 ∈ Image(delta, Traces x y) and r2 ∈ Image(delta, Traces y z),
  -- we show d(x, z) ≤ r1 + r2.
  -- Then d(x, z) ≤ inf(r1) + inf(r2) by properties of sInf.
  unfold d
  apply le_csInf_add
  · rcases h_xy with ⟨R, hR⟩; use delta S R, R, hR, rfl
  · rcases h_yz with ⟨R, hR⟩; use delta S R, R, hR, rfl
  · intro r1 hr1 r2 hr2
    rcases hr1 with ⟨R₁, hR₁, rfl⟩
    rcases hr2 with ⟨R₂, hR₂, rfl⟩
    rcases hR₁ with ⟨h_src1, h_dst1⟩
    rcases hR₂ with ⟨h_src2, h_dst2⟩
    have h_mid : T.dst R₁ = T.src R₂ := h_dst1.trans h_src2.symm
    rcases T.comp_defined h_mid with ⟨R₂₁, hcomp⟩
    have h_xz : R₂₁ ∈ Traces S T x z := by
      simp [Traces]
      constructor
      · rw [T.comp_src hcomp, h_src1]
      · rw [T.comp_dst hcomp, h_dst2]
    have h_delta : delta S R₂₁ ≤ delta S R₂ + delta S R₁ := delta_subadd A hcomp
    have h_in_xz : delta S R₂₁ ∈ delta S '' Traces S T x z := ⟨R₂₁, h_xz, rfl⟩
    have h_bdd : BddBelow (delta S '' Traces S T x z) := by
      use 0
      intro r hr
      rcases hr with ⟨R, _, rfl⟩
      exact delta_nonneg A.toAssumptions R
    calc
      sInf (delta S '' Traces S T x z) ≤ delta S R₂₁ := csInf_le h_bdd h_in_xz
      _ ≤ delta S R₂ + delta S R₁ := h_delta
      _ = r2 + r1 := by simp [add_comm]

end Coh.V2
