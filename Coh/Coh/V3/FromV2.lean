import Mathlib.Data.Rat.Lemmas
import Coh.V2.Geometry
import Coh.V2.Analytic
import Coh.V3.Distance

/-!
## Coh V2 → V3 Bridge (Rational Version)

This module induces a V3 DirectedQuasiMetric from a V2 TransitionSystem
using strictly rational types.
-/

namespace Coh.V3.FromV2

open Coh.V2

/--
  Main Bridge Theorem: V2 → V3 induces directed quasi-metric.
  We package the TransitionSystem into a RationalMetricSystem.
-/
def bridge_to_v3 {S : System} (A : Assumptions S)
    {X : Type} (T : TransitionSystem S X)
    (d_witness : X → X → ENNRat)
    (d_is_inf : ∀ x y, IsRationalInf (ENNRat.ofRat ∘ delta S '' Traces S T x y) (d_witness x y)) :
    DirectedQuasiMetric X :=
  v2TraceSystem_induces_directedQuasiMetric
    { T := fun x y => Traces S T x y
      delta := S.delta
      delta_nonneg := A.delta_nonneg
      comp := fun τ₂ τ₁ =>
        match S.Obs.comp τ₂ τ₁ with
        | some τ₂₁ => τ₂₁
        | none => τ₁ -- Default case, should be unreachable due to T.comp_defined
      comp_closed := by
        intro x y z τ₁ hτ₁ τ₂ hτ₂
        dsimp [Traces] at *
        rcases T.comp_defined (by rw [hτ₁.2, hτ₂.1]) with ⟨τ₂₁, h_eq⟩
        simp [h_eq]
        exact ⟨T.comp_src h_eq, T.comp_dst h_eq⟩
      idTrace := fun _ => S.Obs.id
      id_mem := fun x => by
        simp [Traces]
        exact T.id_state x
      delta_id := fun _ => A.delta_id
      delta_comp := by
        intro x y z τ₁ hτ₁ τ₂ hτ₂
        dsimp
        rcases T.comp_defined (by rw [hτ₁.2, hτ₂.1]) with ⟨τ₂₁, h_eq⟩
        simp [h_eq]
        exact A.delta_subadd h_eq
      d_witness := d_witness
      d_is_inf := d_is_inf }


end Coh.V3.FromV2
