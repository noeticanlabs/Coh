import Coh.V2.Axioms
import Mathlib.Data.Rat.Lemmas
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith

/-!
## Coh V2 Analytic Properties

This module derives the analytical properties of the observable defect envelope (delta),
specifically its subadditivity and its behavior on the identity trace.
-/

noncomputable section

namespace Coh.V2

/--
The delta function is zero at the identity.
Verified via the identity fiber zero-cost and non-emptiness axioms.
-/
theorem delta_id {S : System} (A : Assumptions S) : delta S S.Obs.id = 0 := by
  unfold delta CostSet Fiber
  have h_nonempty : ({c | ∃ ξ, S.proj ξ = S.Obs.id ∧ S.Hid.cost ξ = c} : Set ℚ).Nonempty := by
    rcases A.fiber_nonempty S.Obs.id with ⟨ξ, hξ⟩
    use S.Hid.cost ξ
    exact ⟨ξ, hξ, rfl⟩
  have h_all_zero : ∀ c ∈ {c | ∃ ξ, S.proj ξ = S.Obs.id ∧ S.Hid.cost ξ = c}, c = 0 := by
    intro c hc
    rcases hc with ⟨ξ, hξ, rfl⟩
    exact A.id_fiber_zero ξ hξ
  apply le_antisymm
  · apply rat_csSup_le h_nonempty
    intro c hc
    rw [h_all_zero c hc]
  · rcases h_nonempty with ⟨c, hc⟩
    rw [h_all_zero c hc] at hc
    apply rat_le_csSup (A.fiber_bounded S.Obs.id) hc

/--
The delta function is subadditive.
Verified via the fiber decomposition and hidden cost additivity axioms.
-/
theorem delta_subadd {S : System} (A : SegmentableAssumptions S)
    {R₁ R₂ R₂₁ : S.Obs.V} (hc : S.Obs.comp R₂ R₁ = some R₂₁) :
    delta S R₂₁ ≤ delta S R₂ + delta S R₁ := by
  unfold delta
  have h_nonempty : (CostSet S R₂₁).Nonempty := by
    rcases A.toAssumptions.fiber_nonempty R₂₁ with ⟨ξ, hξ⟩
    use S.Hid.cost ξ
    exact ⟨ξ, hξ, rfl⟩
  apply rat_csSup_le h_nonempty
  intro c h_mem
  rcases h_mem with ⟨ξ, hξ, rfl⟩
  rcases A.toSegmentable.fiber_decomp hc hξ with ⟨ξ₂, ξ₁, h_hcomp, hξ₂, hξ₁⟩
  have h_add := A.toAssumptions.hidden_cost_add h_hcomp
  rw [h_add]
  have h_le₂ : S.Hid.cost ξ₂ ≤ sSup (CostSet S R₂) := by
    apply rat_le_csSup (A.toAssumptions.fiber_bounded R₂)
    exact ⟨ξ₂, hξ₂, rfl⟩
  have h_le₁ : S.Hid.cost ξ₁ ≤ sSup (CostSet S R₁) := by
    apply rat_le_csSup (A.toAssumptions.fiber_bounded R₁)
    exact ⟨ξ₁, hξ₁, rfl⟩
  exact add_le_add h_le₂ h_le₁

/--
The delta function is non-negative.
Verified via the cost non-negativity and fiber non-emptiness axioms.
-/
theorem delta_nonneg {S : System} (A : Assumptions S) (R : S.Obs.V) :
    0 ≤ delta S R := by
  unfold delta
  rcases A.fiber_nonempty R with ⟨ξ, hξ⟩
  let c := S.Hid.cost ξ
  have hc : c ∈ CostSet S R := ⟨ξ, hξ, rfl⟩
  have h_c_le : c ≤ sSup (CostSet S R) := rat_le_csSup (A.fiber_bounded R) hc
  exact (A.cost_nonneg ξ).trans h_c_le

end Coh.V2
