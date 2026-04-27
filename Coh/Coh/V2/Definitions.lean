import Coh.V2.Primitive
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.NNRat.Defs
import Mathlib.Algebra.Order.Monoid.WithTop

/-! ## Coh V2 Definitions -/

namespace Coh.V2

/-- Extended Non-negative Rational type (ℚ≥0 ∪ {∞}). -/
abbrev ENNRat := WithTop NNRat

namespace ENNRat

instance : Zero ENNRat := ⟨WithTop.some 0⟩
instance : One ENNRat := ⟨WithTop.some 1⟩
instance : Bot ENNRat := ⟨0⟩
instance : Top ENNRat := ⟨⊤⟩

/-- Helper to create ENNRat from Rat. -/
def ofRat (q : ℚ) : ENNRat :=
  if h : 0 ≤ q then WithTop.some ⟨q, h⟩ else 0

end ENNRat

variable (S : System) (R : S.Obs.V)

/-- Hidden fiber over an observable trace. -/
def Fiber : Set S.Hid.G :=
  { ξ | S.proj ξ = R }

/-- Fiber cost set in `ℚ` (verifier layer). -/
def CostSetQ : Set ℚ :=
  { q | ∃ ξ : S.Hid.G, ξ ∈ Fiber S R ∧ S.Hid.cost ξ = q }

/-- Alias for backward compatibility. -/
def CostSet : Set ℚ :=
  CostSetQ S R

/-- Observable defect envelope (delta) is now a sealed rational field of the system. -/
def delta (S : System) (R : S.Obs.V) : ℚ :=
  S.delta R

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

end Coh.V2
