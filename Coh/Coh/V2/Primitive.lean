import Mathlib.Data.Rat.Lemmas

/-!
## Coh V2 Primitive Structures

This module defines the core structures for the Coh V2 framework.
-/

namespace Coh.V2

universe u

/-- Hidden realizations with partial composition and exact hidden cost. -/
structure HiddenSystem where
  G : Type u
  comp : G → G → Option G
  cost : G → ℚ

/-- Observable traces with partial composition and observable identity. -/
structure ObservableSystem where
  V : Type u
  comp : V → V → Option V
  id : V
  complexity : V → ℚ

/-- Full Coh V2 system: hidden layer, observable layer, and projection. -/
structure System where
  Hid : HiddenSystem
  Obs : ObservableSystem
  proj : Hid.G → Obs.V
  proj_comp :
    ∀ ξ₂ ξ₁ ξ,
      Hid.comp ξ₂ ξ₁ = some ξ →
      Obs.comp (proj ξ₂) (proj ξ₁) = some (proj ξ)
  /--
    Sealed Defect Envelope: The generator must provide a rational upper bound
    on the fiber costs for each observable trace.
  -/
  delta : Obs.V → ℚ

/--
Inductive structure for explicitly building composite witnesses.
-/
inductive CompositeWitness (S : System) : S.Obs.V → Type u
| atomic : ∀ (ξ : S.Hid.G), CompositeWitness S (S.proj ξ)
| compose : ∀ {R₁ R₂ R₂₁}, S.Obs.comp R₂ R₁ = some R₂₁ →
    CompositeWitness S R₂ → CompositeWitness S R₁ → CompositeWitness S R₂₁

end Coh.V2
