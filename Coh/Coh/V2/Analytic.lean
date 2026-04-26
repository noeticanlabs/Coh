import Coh.V2.Axioms
import Mathlib.Data.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
## Coh V2 Analytic Properties

This module derives the analytical properties of the observable defect envelope (delta),
specifically its non-negativity and behavior on the identity trace.
-/

namespace Coh.V2

noncomputable section

variable {S : System} (A : Assumptions S) (R : S.Obs.V)

/--
The delta function is zero at the identity.
Verified via the identity fiber zero-cost and non-emptiness axioms.
-/
theorem delta_id : delta S S.Obs.id = 0 := by
  unfold delta CostSetReal CostSetQ Fiber
  have h_nonempty : (CostSetReal S S.Obs.id).Nonempty := by
    rcases A.fiber_nonempty S.Obs.id with ⟨ξ, hξ⟩
    use (S.Hid.cost ξ : ℝ)
    exact ⟨S.Hid.cost ξ, ⟨ξ, hξ, rfl⟩, rfl⟩
  have h_all_zero : ∀ r ∈ CostSetReal S S.Obs.id, r = 0 := by
    intro r hr
    rcases hr with ⟨q, ⟨ξ, hξ, rfl⟩, rfl⟩
    simp only [Rat.cast_eq_zero]
    exact A.id_fiber_zero ξ hξ
  apply le_antisymm
  · apply csSup_le h_nonempty
    intro r hr
    rw [h_all_zero r hr]
  · rcases h_nonempty with ⟨r, hr⟩
    rw [h_all_zero r hr] at hr
    apply le_csSup (by simpa) hr

/--
The delta function is non-negative.
Verified via the cost non-negativity and fiber non-emptiness axioms.
-/
theorem delta_nonneg : 0 ≤ delta S R := by
  unfold delta
  rcases A.fiber_nonempty R with ⟨ξ, hξ⟩
  let c := S.Hid.cost ξ
  have hc : c ∈ CostSetQ S R := ⟨ξ, hξ, rfl⟩
  have h_r : (c : ℝ) ∈ CostSetReal S R := by
    exact ⟨c, hc, rfl⟩
  have h_c_le : (c : ℝ) ≤ sSup (CostSetReal S R) := le_csSup (A.fiber_bounded R) h_r
  exact (A.cost_nonneg ξ).trans h_c_le

/--
The delta function is bounded by any upper bound on the fiber cost set.
-/
theorem delta_le_of_bounded {B : ℝ} (hB : ∀ q ∈ CostSetQ S R, (q : ℝ) ≤ B) :
    delta S R ≤ B := by
  unfold delta
  apply csSup_le (A.fiber_nonempty R).costSetReal_nonempty
  intro r hr
  rcases hr with ⟨q, hq, rfl⟩
  exact hB q hq

/--
The delta function is subadditive.
delta(R₂₁ ∘ R₁) ≤ delta(R₂) + delta(R₁)
Verified via fiber decomposition and cost additivity.
-/
theorem delta_subadd (Seg : Segmentable S) {R₁ R₂ R₂₁ : S.Obs.V}
    (hc : S.Obs.comp R₂ R₁ = some R₂₁) :
    delta S R₂₁ ≤ delta S R₂ + delta S R₁ := by
  unfold delta
  apply csSup_le (A.fiber_nonempty R₂₁).costSetReal_nonempty
  intro r hr
  rcases hr with ⟨q, ⟨ξ, hξ, rfl⟩, rfl⟩
  rcases Seg.fiber_decomp hc hξ with ⟨ξ₂, ξ₁, hcomp, hξ₂, hξ₁⟩
  have h_cost : (S.Hid.cost ξ : ℝ) = (S.Hid.cost ξ₂ : ℝ) + (S.Hid.cost ξ₁ : ℝ) := by
    rw [← Rat.cast_add]
    congr
    exact (A.hidden_cost_add hcomp).symm
  rw [h_cost]
  apply add_le_add
  · apply le_csSup (A.fiber_bounded R₂)
    exists (S.Hid.cost ξ₂)
  · apply le_csSup (A.fiber_bounded R₁)
    exists (S.Hid.cost ξ₁)

/--
Distance defined as the defect envelope of the transition trace.
-/
def dist (R : S.Obs.V) : ℝ := delta S R

/--
The triangle inequality for the Coh distance.
d(R₂₁) ≤ d(R₂) + d(R₁)
-/
theorem distance_triangle (Seg : Segmentable S) {R₁ R₂ R₂₁ : S.Obs.V}
    (hc : S.Obs.comp R₂ R₁ = some R₂₁) :
    dist S R₂₁ ≤ dist S R₂ + dist S R₁ :=
  delta_subadd A Seg hc

end Coh.V2
