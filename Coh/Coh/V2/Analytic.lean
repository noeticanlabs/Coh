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
The delta function is zero at the identity.
Verified via the identity fiber zero-cost and non-emptiness axioms.
-/
theorem delta_id {S : System} (A : Assumptions S) : delta S S.Obs.id = 0 := by
  unfold delta CostSet Fiber
  have h_nonempty : ({c | ∃ ξ, S.proj ξ = S.Obs.id ∧ S.Hid.cost ξ = c} : Set ℝ).Nonempty := by
    rcases A.fiber_nonempty S.Obs.id with ⟨ξ, hξ⟩
    use S.Hid.cost ξ
    use ξ
  have h_all_zero : ∀ c ∈ {c | ∃ ξ, S.proj ξ = S.Obs.id ∧ S.Hid.cost ξ = c}, c = 0 := by
    intro c hc
    rcases hc with ⟨ξ, hξ, rfl⟩
    exact A.id_fiber_zero ξ hξ
  apply sSup_eq_of_forall_le_of_forall_ge_of_exists h_nonempty
  · intro c hc; rw [h_all_zero c hc]
  · intro b hb
    rcases h_nonempty with ⟨c, hc⟩
    rw [h_all_zero c hc] at hc ⊢
    exact hb hc

/--
The delta function is subadditive.
Verified via the fiber decomposition and hidden cost additivity axioms.
-/
theorem delta_subadd {S : System} (A : Assumptions S)
    {R₁ R₂ R₂₁ : S.Obs.V} (hc : S.Obs.comp R₂ R₁ = some R₂₁) :
    delta S R₂₁ ≤ delta S R₂ + delta S R₁ := by
  unfold delta
  apply csSup_le (A.fiber_nonempty R₂₁)
  intro c h_mem
  rcases h_mem with ⟨ξ, hξ, rfl⟩
  rcases A.fiber_decomp hc hξ with ⟨ξ₂, ξ₁, h_hcomp, hξ₂, hξ₁⟩
  have h_add := A.hidden_cost_add h_hcomp
  rw [h_add]
  have h_le₂ : S.Hid.cost ξ₂ ≤ sSup (CostSet S R₂) := by
    apply le_csSup (A.fiber_bounded R₂)
    use ξ₂
  have h_le₁ : S.Hid.cost ξ₁ ≤ sSup (CostSet S R₁) := by
    apply le_csSup (A.fiber_bounded R₁)
    use ξ₁
  exact add_le_add h_le₂ h_le₁

end Coh.V2
