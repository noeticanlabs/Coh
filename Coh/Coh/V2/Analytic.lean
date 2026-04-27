import Coh.V2.Axioms
import Mathlib.Data.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.Rat.Lemmas

/-!
## Coh V2 Analytic Properties

This module derives the analytical properties of the observable defect envelope [`delta`](Coh/Coh/V2/Definitions.lean:31).
-/

namespace Coh.V2

open Coh.V2

private theorem costSetReal_nonempty {S : System} (A : Assumptions S) (R : S.Obs.V) :
    (CostSetReal S R).Nonempty := by
  rcases A.fiber_nonempty R with ⟨ξ, hξ⟩
  refine ⟨(S.Hid.cost ξ : ℝ), ?_⟩
  refine ⟨S.Hid.cost ξ, ?_, rfl⟩
  exact ⟨ξ, hξ, rfl⟩

private theorem bddAbove_costSetReal {S : System} (A : Assumptions S) (R : S.Obs.V) :
    BddAbove (CostSetReal S R) := by
  rcases A.fiber_bounded R with ⟨b, hb⟩
  refine ⟨(b : ℝ), ?_⟩
  intro r hr
  rcases hr with ⟨q, hq, rfl⟩
  have hqb : q ≤ b := hb hq
  exact_mod_cast hqb

private theorem cost_mem_costSetReal {S : System} {R : S.Obs.V} {ξ : S.Hid.G}
    (hξ : ξ ∈ Fiber S R) : ((S.Hid.cost ξ : ℝ) ∈ CostSetReal S R) := by
  refine ⟨S.Hid.cost ξ, ?_, rfl⟩
  exact ⟨ξ, hξ, rfl⟩

/--
The delta function is zero at the identity.
-/
theorem delta_id {S : System} (A : Assumptions S) : delta S S.Obs.id = 0 := by
  have hne : (CostSetReal S S.Obs.id).Nonempty :=
    costSetReal_nonempty A S.Obs.id
  apply le_antisymm
  · apply real_csSup_le hne
    intro r hr
    rcases hr with ⟨q, hq, rfl⟩
    rcases hq with ⟨ξ, hξ, rfl⟩
    have hq0 : S.Hid.cost ξ = 0 := A.id_fiber_zero ξ hξ
    exact_mod_cast hq0.le
  · have hmem : (0 : ℝ) ∈ CostSetReal S S.Obs.id := by
      rcases A.fiber_nonempty S.Obs.id with ⟨ξ, hξ⟩
      refine ⟨S.Hid.cost ξ, ?_, ?_⟩
      · exact ⟨ξ, hξ, rfl⟩
      · exact_mod_cast A.id_fiber_zero ξ hξ
    exact real_le_csSup (bddAbove_costSetReal A S.Obs.id) hmem

/--
The delta function is non-negative.
-/
theorem delta_nonneg {S : System} (A : Assumptions S) (R : S.Obs.V) :
    0 ≤ delta S R := by
  rcases A.fiber_nonempty R with ⟨ξ, hξ⟩
  have hcost_nonneg : 0 ≤ (S.Hid.cost ξ : ℝ) := by
    exact_mod_cast A.cost_nonneg ξ
  have hcost_le : (S.Hid.cost ξ : ℝ) ≤ delta S R :=
    real_le_csSup (bddAbove_costSetReal A R) (cost_mem_costSetReal hξ)
  exact le_trans hcost_nonneg hcost_le

/--
The delta function is bounded by any upper bound on the fiber cost set.
-/
theorem delta_le_of_bounded {S : System} {R : S.Obs.V} (A : Assumptions S)
    {B : ℝ} (hB : ∀ q ∈ CostSetQ S R, (q : ℝ) ≤ B) : delta S R ≤ B := by
  apply real_csSup_le (costSetReal_nonempty A R)
  intro r hr
  rcases hr with ⟨q, hq, rfl⟩
  exact hB q hq

/--
The delta function is subadditive under observable composition.
-/
theorem delta_subadd {S : System} (A : SegmentableAssumptions S)
    {R₁ R₂ R₂₁ : S.Obs.V} (hc : S.Obs.comp R₂ R₁ = some R₂₁) :
    delta S R₂₁ ≤ delta S R₂ + delta S R₁ := by
  have hne : (CostSetReal S R₂₁).Nonempty :=
    costSetReal_nonempty A.toAssumptions R₂₁
  apply real_csSup_le hne
  intro r hr
  rcases hr with ⟨q, hq, rfl⟩
  rcases hq with ⟨ξ, hξ, rfl⟩
  rcases A.toSegmentable.fiber_decomp hc hξ with ⟨ξ₂, ξ₁, hcomp, hξ₂, hξ₁⟩
  have hcost : S.Hid.cost ξ = S.Hid.cost ξ₂ + S.Hid.cost ξ₁ :=
    A.toAssumptions.hidden_cost_add hcomp
  have hcostR : (S.Hid.cost ξ : ℝ) = (S.Hid.cost ξ₂ : ℝ) + (S.Hid.cost ξ₁ : ℝ) := by
    exact_mod_cast hcost
  rw [hcostR]
  exact add_le_add
    (real_le_csSup (bddAbove_costSetReal A.toAssumptions R₂) (cost_mem_costSetReal hξ₂))
    (real_le_csSup (bddAbove_costSetReal A.toAssumptions R₁) (cost_mem_costSetReal hξ₁))

end Coh.V2
