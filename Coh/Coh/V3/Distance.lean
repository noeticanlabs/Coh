import Mathlib.Data.Real.Basic
import Mathlib.Data.ENNReal.Operations
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Data.Set.Basic

/-!
## Coh V3 Directed Quasi-Metric
-/

namespace Coh.V3

universe u v

class DirectedQuasiMetric (State : Type u) where
  d : State → State → ENNReal
  d_self : ∀ x : State, d x x = 0
  d_triangle : ∀ x y z : State, d x z ≤ d x y + d y z

namespace DirectedQuasiMetric
variable {State : Type u} [DirectedQuasiMetric State]

theorem d_self_le {x y : State} : d x y ≤ d x x + d x y := by
  rw [d_self]
  exact le_add_self

theorem d_of_zero {x y z : State} (h : d x y = 0) :
    d x z ≤ d y z := by
  have h_tri := d_triangle x y z
  rw [h, zero_add] at h_tri
  exact h_tri

theorem d_triangle_extended (w x y z : State) :
    d w z ≤ d w x + d x y + d y z := by
  calc
    d w z ≤ d w x + d x z := d_triangle w x z
    _ ≤ d w x + (d x y + d y z) := by
      have h := d_triangle x y z
      exact add_le_add_right h (d w x)
    _ = d w x + d x y + d y z := (add_assoc _ _ _).symm
end DirectedQuasiMetric

class V2TraceSystem (State : Type u) (Trace : Type v) where
  T : State → State → Set Trace
  delta : Trace → ℝ
  comp : Trace → Trace → Trace
  comp_closed : ∀ {x y z} (τ₁ : Trace) (_ : τ₁ ∈ T x y) (τ₂ : Trace) (_ : τ₂ ∈ T y z),
    comp τ₂ τ₁ ∈ T x z
  idTrace : State → Trace
  id_mem : ∀ x, idTrace x ∈ T x x
  delta_id : ∀ x, delta (idTrace x) = 0
  delta_comp : ∀ {x y z} (τ₁ : Trace) (_ : τ₁ ∈ T x y) (τ₂ : Trace) (_ : τ₂ ∈ T y z),
    delta (comp τ₂ τ₁) ≤ delta τ₁ + delta τ₂
  delta_nonneg : ∀ τ, 0 ≤ delta τ

open Classical

noncomputable
def dFromV2 {State : Type u} {Trace : Type v} (S : V2TraceSystem State Trace)
    (x y : State) : ENNReal :=
  sInf (ENNReal.ofReal '' (S.delta '' S.T x y))

/-- Helper: if `a ≤ f(i) + g(j)` for all `i ∈ s, j ∈ t`, then `a ≤ sInf (f '' s) + sInf (g '' t)`.
    We prove this via `le_iInf_add_iInf` from Mathlib. -/
theorem le_sInf_image_add_sInf_image
    {α β : Type*} {s : Set α} {t : Set β}
    {f : α → ENNReal} {g : β → ENNReal} {a : ENNReal}
    (h : ∀ x ∈ s, ∀ y ∈ t, a ≤ f x + g y) :
    a ≤ sInf (f '' s) + sInf (g '' t) := by
  simp only [sInf_image]
  exact ENNReal.le_iInf₂_add_iInf₂ h

@[reducible]
noncomputable
def v2TraceSystem_induces_directedQuasiMetric
    {State : Type u} {Trace : Type v} (S : V2TraceSystem State Trace) :
    DirectedQuasiMetric State :=
  {
    d := dFromV2 S
    d_self := by
      intro x
      unfold dFromV2
      apply le_antisymm
      · apply sInf_le
        refine ⟨S.delta (S.idTrace x), ⟨S.idTrace x, S.id_mem x, rfl⟩, ?_⟩
        rw [S.delta_id x]
        exact ENNReal.ofReal_zero
      · exact zero_le _
    d_triangle := by
      intro x y z
      unfold dFromV2
      -- We show: sInf(ofReal '' (delta '' T x z)) ≤ sInf(ofReal '' (delta '' T x y)) + sInf(ofReal '' (delta '' T y z))
      -- Strategy: for each τ₁ ∈ T x y, τ₂ ∈ T y z, compose to get τ₃ ∈ T x z
      -- and sInf(u) ≤ ofReal(delta τ₃) ≤ ofReal(delta τ₁) + ofReal(delta τ₂)
      -- Then use le_sInf_image_add_sInf_image to close.
      -- Rewrite as images of images:
      -- sInf (ofReal '' (delta '' T x z)) ≤ sInf ((ofReal ∘ delta) '' T x y) + sInf ((ofReal ∘ delta) '' T y z)
      -- But they are already in this form after unfolding Set.image composition.
      rw [Set.image_image, Set.image_image, Set.image_image]
      apply le_sInf_image_add_sInf_image
      intro τ₁ hτ₁ τ₂ hτ₂
      let τ₃ := S.comp τ₂ τ₁
      have hτ₃ : τ₃ ∈ S.T x z := S.comp_closed τ₁ hτ₁ τ₂ hτ₂
      have hδ₃ : S.delta τ₃ ≤ S.delta τ₁ + S.delta τ₂ := S.delta_comp τ₁ hτ₁ τ₂ hτ₂
      calc
        sInf ((fun τ => ENNReal.ofReal (S.delta τ)) '' S.T x z)
          ≤ ENNReal.ofReal (S.delta τ₃) := by
            apply sInf_le
            exact ⟨τ₃, hτ₃, rfl⟩
        _ ≤ ENNReal.ofReal (S.delta τ₁ + S.delta τ₂) :=
            ENNReal.ofReal_le_ofReal hδ₃
        _ ≤ ENNReal.ofReal (S.delta τ₁) + ENNReal.ofReal (S.delta τ₂) :=
            ENNReal.ofReal_add_le
  }

end Coh.V3
