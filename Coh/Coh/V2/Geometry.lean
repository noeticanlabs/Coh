import Coh.V2.Analytic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
## Coh V2 Geometry Layer
-/

namespace Coh.V2

open Coh.V2

noncomputable section

structure TransitionSystem (S : System) (X : Type _) where
  src : S.Obs.V → X
  dst : S.Obs.V → X
  id_state : ∀ x : X, src S.Obs.id = x ∧ dst S.Obs.id = x
  comp_src : ∀ {R₁ R₂ R₂₁}, S.Obs.comp R₂ R₁ = some R₂₁ → src R₂₁ = src R₁
  comp_dst : ∀ {R₁ R₂ R₂₁}, S.Obs.comp R₂ R₁ = some R₂₁ → dst R₂₁ = dst R₂
  comp_mid : ∀ {R₁ R₂ R₂₁}, S.Obs.comp R₂ R₁ = some R₂₁ → dst R₁ = src R₂
  comp_defined : ∀ {R₁ R₂}, dst R₁ = src R₂ → ∃ R₂₁, S.Obs.comp R₂ R₁ = some R₂₁

def Traces (S : System) {X : Type _} (T : TransitionSystem S X) (x y : X) : Set S.Obs.V :=
  { R | T.src R = x ∧ T.dst R = y }

def d {S : System} {X : Type _} (A : Assumptions S) (T : TransitionSystem S X) (x y : X) : ℝ :=
  sInf (delta S '' Traces S T x y)

theorem d_id {S : System} {X : Type _} (A : Assumptions S) (T : TransitionSystem S X) (x : X) :
    d A T x x = 0 := by
  let s := delta S '' Traces S T x x
  have h_id : S.Obs.id ∈ Traces S T x x := ⟨(T.id_state x).1, (T.id_state x).2⟩
  have h_mem : (0 : ℝ) ∈ s := ⟨S.Obs.id, h_id, delta_id A⟩
  have h_bdd : BddBelow s := ⟨0, fun r ⟨R, hR, hr⟩ => hr ▸ delta_nonneg A R⟩
  apply le_antisymm
  · exact csInf_le h_bdd h_mem
  · apply le_csInf ⟨0, h_mem⟩
    intro r hr
    rcases hr with ⟨R, hR, rfl⟩
    exact delta_nonneg A R

theorem d_nonneg {S : System} {X : Type _} (A : Assumptions S) (T : TransitionSystem S X) (x y : X) 
    (h_reachable : (Traces S T x y).Nonempty) :
    0 ≤ d A T x y := by
  let s := delta S '' Traces S T x y
  have hne : s.Nonempty := by
    rcases h_reachable with ⟨R, hR⟩
    exact ⟨delta S R, R, hR, rfl⟩
  apply le_csInf hne
  intro r hr
  rcases hr with ⟨R, hR, rfl⟩
  exact delta_nonneg A R

theorem d_triangle {S : System} (A : SegmentableAssumptions S) {X : Type _} 
    (T : TransitionSystem S X) (x y z : X) 
    (h_xy : (Traces S T x y).Nonempty) (h_yz : (Traces S T y z).Nonempty) :
    d A.toAssumptions T x z ≤ d A.toAssumptions T x y + d A.toAssumptions T y z :=
  by
    let u := delta S '' Traces S T x z
    let s := delta S '' Traces S T x y
    let t := delta S '' Traces S T y z
    have hb_u : BddBelow u := ⟨0, fun r ⟨R, hR, hr⟩ => hr ▸ delta_nonneg A.toAssumptions R⟩
    have hne_s : s.Nonempty := by
      rcases h_xy with ⟨R, hR⟩; exact ⟨delta S R, R, hR, rfl⟩
    have hne_t : t.Nonempty := by
      rcases h_yz with ⟨R, hR⟩; exact ⟨delta S R, R, hR, rfl⟩
    have hb_s : BddBelow s := ⟨0, fun r ⟨R, hR, hr⟩ => hr ▸ delta_nonneg A.toAssumptions R⟩
    have hb_t : BddBelow t := ⟨0, fun r ⟨R, hR, hr⟩ => hr ▸ delta_nonneg A.toAssumptions R⟩
    
    apply le_of_forall_pos_le_add
    intro ε hε
    have h1 : sInf s < sInf s + ε/2 := by linarith
    rcases (csInf_lt_iff hb_s hne_s).mp h1 with ⟨r1, ⟨R1, hR1, rfl⟩, h_r1_lt⟩
    have h2 : sInf t < sInf t + ε/2 := by linarith
    rcases (csInf_lt_iff hb_t hne_t).mp h2 with ⟨r2, ⟨R2, hR2, rfl⟩, h_r2_lt⟩
    
    have h_mid : T.dst R1 = T.src R2 := hR1.2.trans hR2.1.symm
    rcases T.comp_defined h_mid with ⟨R21, hcomp⟩
    have hR21 : R21 ∈ Traces S T x z := ⟨T.comp_src hcomp ▸ hR1.1, T.comp_dst hcomp ▸ hR2.2⟩
    
    calc
      sInf u ≤ delta S R21 := csInf_le hb_u ⟨R21, hR21, rfl⟩
      _ ≤ delta S R1 + delta S R2 := by rw [add_comm]; exact delta_subadd A hcomp
      _ ≤ sInf s + ε/2 + (sInf t + ε/2) := by linarith
      _ = sInf s + sInf t + ε := by linarith

end 

end Coh.V2
