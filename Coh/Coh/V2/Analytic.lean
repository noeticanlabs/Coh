import Coh.V2.Axioms
import Mathlib.Data.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
## Coh V2 Analytic Properties

This module derives the analytical properties of the observable defect envelope (delta),
specifically its subadditivity and its behavior on the identity trace.
-/

noncomputable section

namespace Coh.V2

/--
The observable defect envelope is zero at the identity trace.
This mirrors the manuscript's property that the baseline for an empty trace is zero.
-/
theorem delta_id {S : System} (A : Assumptions S) : delta S S.Obs.id = 0 := by
  unfold delta
  have h_ne : (CostSet S S.Obs.id).Nonempty := by
    rcases A.fiber_nonempty S.Obs.id with ⟨ξ, hξ⟩
    use S.Hid.cost ξ, ξ, hξ, rfl
  have h_bdd : BddAbove (CostSet S S.Obs.id) := A.fiber_bounded S.Obs.id
  apply le_antisymm
  · apply sSup_le h_ne
    intro c hc
    rcases hc with ⟨ξ, hξ, rfl⟩
    exact le_of_eq (A.id_fiber_zero ξ hξ)
  · apply le_sSup h_bdd
    rcases A.fiber_nonempty S.Obs.id with ⟨ξ, hξ⟩
    use S.Hid.cost ξ
    simp [hξ, A.id_fiber_zero ξ hξ]

/--
The observable defect envelope is subadditive under observable composition.
This is the core analytic property used to certify composite morphisms.
-/
theorem delta_subadd {S : System} (A : Assumptions S)
    {R₁ R₂ R₂₁ : S.Obs.V} (hc : S.Obs.comp R₂ R₁ = some R₂₁) :
    delta S R₂₁ ≤ delta S R₂ + delta S R₁ := by
  unfold delta
  have h_ne : (CostSet S R₂₁).Nonempty := by
    rcases A.fiber_nonempty R₂₁ with ⟨ξ, hξ⟩
    use S.Hid.cost ξ, ξ, hξ, rfl
  apply sSup_le h_ne
  intro c hc
  rcases hc with ⟨ξ, hξ, rfl⟩
  rcases A.fiber_decomp hc hξ with ⟨ξ₂, ξ₁, h_comp, hξ₂, hξ₁⟩
  rw [A.hidden_cost_add h_comp]
  apply add_le_add
  · apply le_sSup (A.fiber_bounded R₂)
    use ξ₂, hξ₂, rfl
  · apply le_sSup (A.fiber_bounded R₁)
    use ξ₁, hξ₁, rfl

end Coh.V2
