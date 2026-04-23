import Mathlib.Data.Real.Basic

namespace Coh.V2

universe u

/-- Hidden realizations with partial composition and exact hidden cost. -/
structure HiddenSystem where
  G : Type u
  comp : G → G → Option G
  cost : G → ℝ

/-- Observable traces with partial composition and observable identity. -/
structure ObservableSystem where
  V : Type u
  comp : V → V → Option V
  id : V

/-- Full Coh V2 system: hidden layer, observable layer, and projection. -/
structure System where
  Hid : HiddenSystem
  Obs : ObservableSystem
  proj : Hid.G → Obs.V

end Coh.V2
