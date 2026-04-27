import Mathlib.Data.Real.Basic
import Mathlib.Data.ENNReal.Operations
import Coh.V2.Geometry
import Coh.V2.Analytic
import Coh.V3.Distance

/-!
## Coh V2 → V3 Bridge
-/

namespace Coh.V3.FromV2

open Coh.V2

/--
  V3 distance from V2 data using ENNReal.
-/
noncomputable
def d_Coh {S : System} {X : Type} (A : Assumptions S)
    (T : TransitionSystem S X) (x y : X) : ENNReal :=
  sInf (ENNReal.ofReal '' (delta S '' Traces S T x y))

/--
  Main Bridge Theorem: V2 → V3 induces directed quasi-metric.
-/
@[reducible]
noncomputable
def v2_to_v3_bridge_inst {S : System} (A : SegmentableAssumptions S)
    {X : Type} (T : TransitionSystem S X) :
    DirectedQuasiMetric X :=
  {
    d := fun x y => d_Coh A.toAssumptions T x y
    d_self := by
      intro x
      unfold d_Coh
      apply le_antisymm
      · apply sInf_le
        refine ⟨delta S S.Obs.id, ⟨S.Obs.id, ?_, rfl⟩, ?_⟩
        · exact ⟨(T.id_state x).1, (T.id_state x).2⟩
        · rw [delta_id A.toAssumptions]; exact ENNReal.ofReal_zero
      · exact zero_le _
    d_triangle := by
      intro x y z
      unfold d_Coh
      rw [Set.image_image, Set.image_image, Set.image_image]
      apply le_sInf_image_add_sInf_image
      intro τ₁ hτ₁ τ₂ hτ₂
      have h_mid : T.dst τ₁ = T.src τ₂ := by
        rcases hτ₁ with ⟨_, hdst⟩
        rcases hτ₂ with ⟨hsrc, _⟩
        exact hdst.trans hsrc.symm
      rcases T.comp_defined h_mid with ⟨τ₃, hcomp⟩
      have hτ₃ : τ₃ ∈ Traces S T x z := by
        constructor
        · rw [T.comp_src hcomp]; exact hτ₁.1
        · rw [T.comp_dst hcomp]; exact hτ₂.2
      have hδ : delta S τ₃ ≤ delta S τ₁ + delta S τ₂ := by
        rw [add_comm]
        apply delta_subadd A hcomp
      calc
        sInf ((fun τ => ENNReal.ofReal (delta S τ)) '' Traces S T x z)
          ≤ ENNReal.ofReal (delta S τ₃) := by
            apply sInf_le; exact ⟨τ₃, hτ₃, rfl⟩
        _ ≤ ENNReal.ofReal (delta S τ₁ + delta S τ₂) :=
            ENNReal.ofReal_le_ofReal hδ
        _ ≤ ENNReal.ofReal (delta S τ₁) + ENNReal.ofReal (delta S τ₂) :=
            ENNReal.ofReal_add_le
  }

end Coh.V3.FromV2
