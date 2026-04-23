import Coh.V2.Axioms
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
## Coh V2 Analytic Envelopes

This module develops the analytic theory of the Coh V2 framework.
It defines the defect envelope (delta) as the supremum of costs in the
hidden fiber and proves its soundness, minimality, and subadditivity properties.
-/

noncomputable section

open scoped Classical

namespace Coh.V2

universe u

section Analytic

variable {S : System} (A : Assumptions S)

include A

/-- A hidden witness contributes its cost to the corresponding cost set. -/
lemma cost_mem_CostSet
    {R : S.Obs.V} {ξ : S.Hid.G}
    (hξ : ξ ∈ Fiber S R) :
    S.Hid.cost ξ ∈ CostSet S R := by
  exact ⟨ξ, hξ, rfl⟩

/-- Fiber nonemptiness induces cost-set nonemptiness. -/
lemma CostSet_nonempty (R : S.Obs.V) :
    (CostSet S R).Nonempty := by
  rcases Assumptions.fiber_nonempty A R with ⟨ξ, hξ⟩
  exact ⟨S.Hid.cost ξ, ⟨ξ, hξ, rfl⟩⟩

/-- Envelope soundness: every hidden witness is bounded by the envelope. -/
theorem envelope_soundness
    {R : S.Obs.V} {ξ : S.Hid.G}
    (hξ : ξ ∈ Fiber S R) :
    S.Hid.cost ξ ≤ delta S R := by
  exact le_csSup (Assumptions.fiber_bounded A R) (cost_mem_CostSet A hξ)

/-- Envelope minimality: every common upper bound dominates the envelope. -/
theorem envelope_minimality
    {R : S.Obs.V} {c : ℝ}
    (hc : ∀ ξ ∈ Fiber S R, S.Hid.cost ξ ≤ c) :
    delta S R ≤ c := by
  refine csSup_le (CostSet_nonempty A R) ?_
  intro x hx
  rcases hx with ⟨ξ, hξ, hcost⟩
  rw [← hcost]
  exact hc ξ hξ

/-- Identity envelope is zero. -/
theorem delta_id:
    delta S S.Obs.id = 0 := by
  apply le_antisymm
  · exact envelope_minimality A (R := S.Obs.id) (c := 0)
      (fun ξ hξ => by simpa [Assumptions.id_fiber_zero A ξ hξ])
  · rcases Assumptions.fiber_nonempty A S.Obs.id with ⟨ξ, hξ⟩
    have hzero : S.Hid.cost ξ = 0 := Assumptions.id_fiber_zero A ξ hξ
    have hsnd : S.Hid.cost ξ ≤ delta S S.Obs.id :=
      envelope_soundness A hξ
    simpa [hzero] using hsnd

/--
Pointwise bound on a hidden witness in a composite observable fiber.
This is the manuscript's decomposition-first route.
-/
theorem pointwise_composite_bound
    {R₁ R₂ R₂₁ : S.Obs.V}
    (hcomp : S.Obs.comp R₂ R₁ = some R₂₁)
    {ξ : S.Hid.G}
    (hξ : ξ ∈ Fiber S R₂₁) :
    S.Hid.cost ξ ≤ delta S R₁ + delta S R₂ := by
  rcases Assumptions.fiber_decomp A hcomp hξ with ⟨ξ₂, ξ₁, hhid, hξ₂, hξ₁⟩
  have hadd : S.Hid.cost ξ = S.Hid.cost ξ₂ + S.Hid.cost ξ₁ :=
    Assumptions.hidden_cost_add A hhid
  have h₁ : S.Hid.cost ξ₁ ≤ delta S R₁ :=
    envelope_soundness A hξ₁
  have h₂ : S.Hid.cost ξ₂ ≤ delta S R₂ :=
    envelope_soundness A hξ₂
  have hs : S.Hid.cost ξ₂ + S.Hid.cost ξ₁ ≤ delta S R₂ + delta S R₁ :=
    add_le_add h₂ h₁
  calc
    S.Hid.cost ξ = S.Hid.cost ξ₂ + S.Hid.cost ξ₁ := hadd
    _ ≤ delta S R₂ + delta S R₁ := hs
    _ = delta S R₁ + delta S R₂ := by simpa [add_comm, add_left_comm, add_assoc]

/-- Projection-induced subadditivity of the observable defect envelope. -/
theorem delta_subadd
    {R₁ R₂ R₂₁ : S.Obs.V}
    (hcomp : S.Obs.comp R₂ R₁ = some R₂₁) :
    delta S R₂₁ ≤ delta S R₁ + delta S R₂ := by
  exact envelope_minimality A (R := R₂₁)
    (c := delta S R₁ + delta S R₂)
    (fun ξ hξ => pointwise_composite_bound A hcomp hξ)

end Analytic

end Coh.V2
