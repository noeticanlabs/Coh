import Coh.V2.Primitive
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-! ## Coh V2 Definitions -/

namespace Coh.V2

noncomputable section

variable (S : System) (R : S.Obs.V)

/-- Hidden fiber over an observable trace. -/
def Fiber : Set S.Hid.G :=
  { ξ | S.proj ξ = R }

/-- Fiber cost set in `ℚ` (verifier layer). -/
def CostSetQ : Set ℚ :=
  { q | ∃ ξ : S.Hid.G, ξ ∈ Fiber S R ∧ S.Hid.cost ξ = q }

/-- Alias for backward compatibility with modules expecting CostSet (ℚ version). -/
def CostSet : Set ℚ :=
  CostSetQ S R

/-- Fiber cost set in `ℝ` (analytic layer). -/
def CostSetReal : Set ℝ :=
  { r | ∃ q : ℚ, q ∈ CostSetQ S R ∧ (q : ℝ) = r }

/-- Observable defect envelope (delta) defined in ℝ to ensure supremum-completeness. -/
def delta (S : System) (R : S.Obs.V) : ℝ :=
  sSup (CostSetReal S R)

/-- A system is segmentable if its hidden witness carrier allows for
    decomposition of composite traces into their respective components. -/
structure Segmentable (S : System) : Prop where
  fiber_decomp :
    ∀ {R₁ R₂ R₂₁ : S.Obs.V} {ξ : S.Hid.G},
      S.Obs.comp R₂ R₁ = some R₂₁ →
      ξ ∈ Fiber S R₂₁ →
      ∃ ξ₂ ξ₁,
        S.Hid.comp ξ₂ ξ₁ = some ξ ∧
        ξ₂ ∈ Fiber S R₂ ∧
        ξ₁ ∈ Fiber S R₁

theorem real_le_csSup {s : Set ℝ} {a : ℝ} (hb : BddAbove s) (ha : a ∈ s) : a ≤ sSup s :=
  le_csSup hb ha

theorem real_csSup_le {s : Set ℝ} {a : ℝ} (hne : s.Nonempty) (ha : ∀ x ∈ s, x ≤ a) : sSup s ≤ a :=
  csSup_le hne ha

end

end Coh.V2
