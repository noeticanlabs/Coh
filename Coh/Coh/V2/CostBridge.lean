import Coh.V1.Coh
import Coh.V2.FiniteWord
import Mathlib.Data.Rat.Lemmas

/-!
## Coh V1 to V2 Cost Bridge
-/

namespace Coh.V2.CostBridge

open Coh.V1
open Coh.V2.FiniteWord

/-- Translation from V1 traceSpend to V2 hiddenCost. -/
theorem trace_spend_eq_hidden_cost {X : Type} (t : Trace X) :
    traceSpend t = hiddenCost X (Coh.V1.Step X) (fun s => s.costSpend) (t.steps.map fun s => (s.src, s)) :=
  by
    unfold traceSpend hiddenCost
    generalize t.steps = l
    induction l with
    | nil => simp [stepsSpend]
    | cons s ss ih =>
      simp only [stepsSpend, List.map_cons, List.sum_cons]
      rw [ih]

end Coh.V2.CostBridge
