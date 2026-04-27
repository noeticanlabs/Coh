import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.NNRat.Defs
import Mathlib.Algebra.Order.Monoid.WithTop
import Coh.V2.Definitions

/-!
## Coh V3 Directed Quasi-Metric (Rational-Only)

This module defines the directed quasi-metric structure using strictly rational types
to ensure computational determinism.
-/

namespace Coh.V3

open Coh.V2

-- Missing instances for ENNRat (WithTop NNRat)
instance : CanonicallyOrderedAdd ENNRat := WithTop.instCanonicallyOrderedAddWithTop
instance : AddLeftMono ENNRat := WithTop.instAddLeftMonoWithTop

/--
  Directed Quasi-Metric Class (Rational Version).
  Uses ENNRat to represent distances, including infinity for unreachable states.
-/
class DirectedQuasiMetric (State : Type _) where
  d : State → State → ENNRat
  d_self : ∀ x : State, d x x = 0
  d_triangle : ∀ x y z : State, d x z ≤ d x y + d y z

namespace DirectedQuasiMetric
variable {State : Type _} [DirectedQuasiMetric State]

theorem d_of_zero {x y z : State} (h : d x y = 0) :
    d x z ≤ d y z := by
  have h_tri := d_triangle x y z
  rw [h] at h_tri
  have h_zero_add : (0 : ENNRat) + d y z = d y z := by
    simp [Zero.zero, Add.add]
    cases d y z <;> rfl
  rw [h_zero_add] at h_tri
  exact h_tri

end DirectedQuasiMetric

/--
  V2 Trace System (Rational Version).
  All costs and metrics are strictly rational.
-/
class V2TraceSystem (State : Type _) (Trace : Type _) where
  T : State → State → Set Trace
  delta : Trace → ℚ
  delta_nonneg : ∀ τ, 0 ≤ delta τ
  comp : Trace → Trace → Trace
  comp_closed : ∀ {x y z} (τ₁ : Trace) (_ : τ₁ ∈ T x y) (τ₂ : Trace) (_ : τ₂ ∈ T y z),
    comp τ₂ τ₁ ∈ T x z
  idTrace : State → Trace
  id_mem : ∀ x, idTrace x ∈ T x x
  delta_id : ∀ x, delta (idTrace x) = 0
  delta_comp : ∀ {x y z} (τ₁ : Trace) (_ : τ₁ ∈ T x y) (τ₂ : Trace) (_ : τ₂ ∈ T y z),
    delta (comp τ₂ τ₁) ≤ delta τ₁ + delta τ₂

open Classical

/--
  Helper: Rational infimum properties.
  Since ℚ is not complete, we define the properties we need as a predicate
  or assume the system admits a rational infimum.
-/
def IsRationalInf (s : Set ENNRat) (i : ENNRat) : Prop :=
  (∀ x ∈ s, i ≤ x) ∧ (∀ j, (∀ x ∈ s, j ≤ x) → j ≤ i)

/--
  Lemma: Infimum addition property for rational sets.
  Ensures that the sum of infima is a lower bound for the sum of elements.
-/
theorem le_inf_add_inf {s1 s2 : Set ENNRat} {i1 i2 : ENNRat}
    (h1 : IsRationalInf s1 i1) (h2 : IsRationalInf s2 i2) :
    ∀ x ∈ s1, ∀ y ∈ s2, i1 + i2 ≤ x + y := by
  intro x hx y hy
  exact add_le_add (h1.1 x hx) (h2.1 y hy)

/--
  Induce a DirectedQuasiMetric from a V2TraceSystem.
  Note: This assumes the existence of a rational infimum for each trace set.
-/
structure RationalMetricSystem (State : Type _) (Trace : Type _) extends V2TraceSystem State Trace where
  d_witness : State → State → ENNRat
  d_is_inf : ∀ x y, IsRationalInf ((fun τ => ENNRat.ofRat (delta τ)) '' T x y) (d_witness x y)

noncomputable
def v2TraceSystem_induces_directedQuasiMetric
    {State : Type _} {Trace : Type _} (S : RationalMetricSystem State Trace) :
    DirectedQuasiMetric State :=
  {
    d := S.d_witness
    d_self := by
      intro x
      rcases S.d_is_inf x x with ⟨h_low, h_great⟩
      apply le_antisymm
      · apply h_low 0
        exact ⟨S.idTrace x, S.id_mem x, by simp [ENNRat.ofRat, S.delta_id x]⟩
      · apply h_great 0
        intro d' hd'
        rcases hd' with ⟨τ, _, rfl⟩
        simp [ENNRat.ofRat]
        split_ifs with h
        · apply WithTop.coe_le_coe.mpr
          exact S.delta_nonneg τ
        · exact le_refl _
    d_triangle := by
      intro x y z
      rcases S.d_is_inf x y with ⟨h_low_xy, h_great_xy⟩
      rcases S.d_is_inf y z with ⟨h_low_yz, h_great_yz⟩
      rcases S.d_is_inf x z with ⟨h_low_xz, h_great_xz⟩
      
      have h_bound : ∀ (τ₁ : Trace) (_ : τ₁ ∈ S.T x y) (τ₂ : Trace) (_ : τ₂ ∈ S.T y z),
          S.d_witness x z ≤ ENNRat.ofRat (S.delta τ₁) + ENNRat.ofRat (S.delta τ₂) := by
        intro τ₁ hτ₁ τ₂ hτ₂
        apply h_low_xz
        use S.comp τ₂ τ₁
        use S.comp_closed τ₁ hτ₁ τ₂ hτ₂
        simp [ENNRat.ofRat]
        split_ifs with h_pos
        · apply WithTop.coe_le_coe.mpr
          exact S.delta_comp τ₁ hτ₁ τ₂ hτ₂
        · have := S.delta_nonneg (S.comp τ₂ τ₁)
          linarith

      have h1 : ∀ (τ₁ : Trace) (hτ₁ : τ₁ ∈ S.T x y),
          S.d_witness x z ≤ ENNRat.ofRat (S.delta τ₁) + S.d_witness y z := by
        intro τ₁ hτ₁
        apply h_great_yz
        intro j' hj'
        rcases hj' with ⟨τ₂, hτ₂, rfl⟩
        exact h_bound τ₁ hτ₁ τ₂ hτ₂
      
      apply h_great_xy
      intro j'' hj''
      rcases hj'' with ⟨τ₁, hτ₁, rfl⟩
      rw [add_comm]
      exact h1 τ₁ hτ₁
  }


end Coh.V3
