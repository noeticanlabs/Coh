import Mathlib.Data.Rat.Lemmas

/-!
## Coh V2 Primitive Structures

This module defines the core structures for the Coh V2 framework,
separating hidden execution layers from observable trace layers.
-/

namespace Coh.V2

universe u

/-- Hidden realizations with partial composition and exact hidden cost. -/
structure HiddenSystem where
  /-- The set of hidden execution traces. -/
  G : Type u
  /-- Partial composition of hidden traces. -/
  comp : G → G → Option G
  /-- Exact cost of a hidden trace in `ℚ`. -/
  cost : G → ℚ

/-- Observable traces with partial composition and observable identity. -/
structure ObservableSystem where
  /-- The set of observable traces. -/
  V : Type u
  /-- Partial composition of observable traces. -/
  comp : V → V → Option V
  /-- The identity (null) observable trace. -/
  id : V

/-- Full Coh V2 system: hidden layer, observable layer, and projection. -/
structure System where
  /-- The hidden system layer. -/
  Hid : HiddenSystem
  /-- The observable system layer. -/
  Obs : ObservableSystem
  /-- Projection from hidden traces to observable traces. -/
  proj : Hid.G → Obs.V

/--
A trace-indexed realization that is explicitly segmentable.
This structure allows hidden witnesses to be built from atomic components
or by composing existing witnesses, mirroring the observable trace structure.
-/
inductive CompositeWitness (Obs : ObservableSystem) (Hid_atomic : HiddenSystem) (proj_atomic : Hid_atomic.G → Obs.V) : Obs.V → Type u where
  | atomic : ∀ (ξ : Hid_atomic.G), CompositeWitness Obs Hid_atomic proj_atomic (proj_atomic ξ)
  | compose : ∀ {R₁ R₂ R₂₁} (ξ₂ : CompositeWitness Obs Hid_atomic proj_atomic R₂) (ξ₁ : CompositeWitness Obs Hid_atomic proj_atomic R₁),
              Obs.comp R₂ R₁ = some R₂₁ →
              CompositeWitness Obs Hid_atomic proj_atomic R₂₁

end Coh.V2
