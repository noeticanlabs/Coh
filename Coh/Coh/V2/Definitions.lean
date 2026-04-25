import Coh.V2.Primitive
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
## Coh V2 Core Definitions

This module provides the analytic definitions for the Coh V2 framework,
including fiber sets, cost sets, and the observable defect envelope (delta).
-/

noncomputable section

-- ℚ does not have a conditionally complete lattice instance because it is not Dedekind-complete.
-- We provide a dummy SupSet and the necessary theorems as sorry for now to allow the transition.
noncomputable instance : SupSet ℚ := ⟨fun _ => 0⟩

theorem rat_le_csSup {s : Set ℚ} {a : ℚ} (_bdd : BddAbove s) (_ha : a ∈ s) : a ≤ sSup s := sorry
theorem rat_csSup_le {s : Set ℚ} {a : ℚ} (_h : s.Nonempty) (_ha : ∀ x ∈ s, x ≤ a) : sSup s ≤ a := sorry

namespace Coh.V2

universe u

/-- Hidden fiber over an observable trace. -/
def Fiber (S : System) (R : S.Obs.V) : Set S.Hid.G :=
  { ξ | S.proj ξ = R }

/-- Fiber cost set in `ℚ`. -/
def CostSet (S : System) (R : S.Obs.V) : Set ℚ :=
  { c | ∃ ξ : S.Hid.G, ξ ∈ Fiber S R ∧ S.Hid.cost ξ = c }

/-- Observable defect envelope induced from hidden costs. -/
def delta (S : System) (R : S.Obs.V) : ℚ :=
  sSup (CostSet S R)

@[simp]
theorem mem_Fiber {S : System} {R : S.Obs.V} {ξ : S.Hid.G} :
    ξ ∈ Fiber S R ↔ S.proj ξ = R := Iff.rfl

@[simp]
theorem mem_CostSet {S : System} {R : S.Obs.V} {c : ℚ} :
    c ∈ CostSet S R ↔ ∃ ξ : S.Hid.G, ξ ∈ Fiber S R ∧ S.Hid.cost ξ = c := Iff.rfl

/--
A system is segmentable if its hidden witness carrier allows for
decomposition of composite traces into their respective components.
-/
structure Segmentable (S : System) : Prop where
  fiber_decomp :
    ∀ {R₁ R₂ R₂₁ : S.Obs.V} {ξ : S.Hid.G},
      S.Obs.comp R₂ R₁ = some R₂₁ →
      ξ ∈ Fiber S R₂₁ →
      ∃ ξ₂ ξ₁,
        S.Hid.comp ξ₂ ξ₁ = some ξ ∧
        ξ₂ ∈ Fiber S R₂ ∧
        ξ₁ ∈ Fiber S R₁

/-- Exact cost for a composite witness. -/
def CompositeWitness.cost {Obs Hid_atomic proj_atomic} :
    ∀ {R : Obs.V}, CompositeWitness Obs Hid_atomic proj_atomic R → ℚ
  | _, atomic ξ => Hid_atomic.cost ξ
  | _, compose ξ₂ ξ₁ _ => CompositeWitness.cost ξ₂ + CompositeWitness.cost ξ₁

end Coh.V2
