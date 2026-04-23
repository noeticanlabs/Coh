/-!
## Coh V2 Primitive Structures

This module defines the core structures for the Coh V2 framework,
separating hidden execution layers from observable trace layers.
-/

import Mathlib.Data.Real.Basic

namespace Coh.V2

universe u

/-- Hidden realizations with partial composition and exact hidden cost. -/
structure HiddenSystem where
  /-- The set of hidden execution traces. -/
  G : Type u
  /-- Partial composition of hidden traces. -/
  comp : G → G → Option G
  /-- Exact cost of a hidden trace in `ℝ`. -/
  cost : G → ℝ

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

end Coh.V2
