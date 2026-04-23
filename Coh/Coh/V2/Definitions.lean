import Coh.V2.Primitive
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean

noncomputable section

namespace Coh.V2

universe u

/-- Hidden fiber over an observable trace. -/
def Fiber (S : System) (R : S.Obs.V) : Set S.Hid.G :=
  { ξ | S.proj ξ = R }

/-- Fiber cost set in `ℝ`. -/
def CostSet (S : System) (R : S.Obs.V) : Set ℝ :=
  { c | ∃ ξ : S.Hid.G, ξ ∈ Fiber S R ∧ S.Hid.cost ξ = c }

/-- Observable defect envelope induced from hidden costs. -/
def delta (S : System) (R : S.Obs.V) : ℝ :=
  sSup (CostSet S R)

@[simp]
theorem mem_Fiber {S : System} {R : S.Obs.V} {ξ : S.Hid.G} :
    ξ ∈ Fiber S R ↔ S.proj ξ = R := Iff.rfl

@[simp]
theorem mem_CostSet {S : System} {R : S.Obs.V} {c : ℝ} :
    c ∈ CostSet S R ↔ ∃ ξ : S.Hid.G, ξ ∈ Fiber S R ∧ S.Hid.cost ξ = c := Iff.rfl

end Coh.V2
