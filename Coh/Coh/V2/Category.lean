import Coh.V2.Certified
import Mathlib.Order.Basic
import Mathlib.Data.Rat.Lemmas

/-!
## Coh V2 Category Theory

This module formalizes the category-theoretic structure of certified morphisms.
It proves that certified morphisms form a locally preordered category,
satisfying associativity and identity laws.
-/

noncomputable section

namespace Coh.V2

universe u v w

/--
A 2-cell in the Coh category representing the optimization slack (parameterized by Δ).
A 2-cell f ⟹ g exists if g is a 'slacker' version of the same transition f.
-/
structure Slack2Cell {S : System} {A : Assumptions S} {X : Type v} {V : X → ℚ}
    {x y : X} (f g : CertifiedMor S A V x y) where
  delta : ℚ
  delta_nonneg : 0 ≤ delta
  eq_trace : f.trace = g.trace
  eq_spend : f.spend = g.spend
  eq_defect : g.defect = f.defect + delta

/--
A 2-category where each hom-set is a partial order (locally posetal).
This aligns with the manuscript's Section 7 definition.
-/
structure LocallyPosetal2Category (Obj : Type u) where
  Hom : Obj → Obj → Type w
  id : ∀ x, Hom x x
  comp : ∀ {x y z}, Hom x y → Hom y z → Hom x z
  /-- 1-cell composition is strictly associative (Syntactic). -/
  comp_assoc :
    ∀ {w x y z} (f : Hom w x) (g : Hom x y) (h : Hom y z),
      comp (comp f g) h = comp f (comp g h)
  id_right : ∀ {x y} (f : Hom x y), comp (id x) f = f
  id_left : ∀ {x y} (f : Hom x y), comp f (id y) = f
  /-- 2-morphisms between parallel 1-morphisms. -/
  TwoCell : ∀ {x y : Obj}, Hom x y → Hom x y → Type w
  two_refl : ∀ {x y} (f : Hom x y), TwoCell f f
  two_trans : ∀ {x y} {f g h : Hom x y}, TwoCell f g → TwoCell g h → TwoCell f h
  two_antisymm : ∀ {x y} {f g : Hom x y}, TwoCell f g → TwoCell g f → f = g
  /-- Horizontal composition (whiskering) is monotone. -/
  comp_monotone :
    ∀ {x y z} {f₁ f₂ : Hom x y} {g₁ g₂ : Hom y z},
      TwoCell f₁ f₂ → TwoCell g₁ g₂ → TwoCell (comp f₁ g₁) (comp f₂ g₂)

/-- Implementation of the Coh 2-category using Syntactic composition. -/
def certified2Category
    (S : System) (A : SegmentableAssumptions S) (X : Type v) (V : X → ℚ)
    (chooseComp :
      ∀ {x y z : X}
        (f : CertifiedMor S A.toAssumptions V x y)
        (g : CertifiedMor S A.toAssumptions V y z),
        Σ' R₂₁ : S.Obs.V, S.Obs.comp g.trace f.trace = some R₂₁) :
    LocallyPosetal2Category X :=
  let idObj : ∀ x : X, CertifiedMor S A.toAssumptions V x x :=
    fun x => idMor V x
  let compObj :
      ∀ {x y z : X},
        CertifiedMor S A.toAssumptions V x y →
        CertifiedMor S A.toAssumptions V y z →
        CertifiedMor S A.toAssumptions V x z :=
    fun {x y z} f g =>
      let p := chooseComp f g
      compose A V f g p.2
  { Hom := fun x y => CertifiedMor S A.toAssumptions V x y,
    id := idObj,
    comp := compObj,
    comp_assoc := fun {w x y z} f g h => assoc_certified A V f g h (chooseComp f g).2 (chooseComp g h).2
        (chooseComp (compObj f g) h).2 (chooseComp f (compObj g h)).2,
    id_right := fun {x y} f => id_right_certified A V f (chooseComp (idObj x) f).2,
    id_left := fun {x y} f => id_left_certified A V f (chooseComp f (idObj y)).2,
    TwoCell := fun f g => Slack2Cell f g,
    two_refl := fun f => { delta := 0, delta_nonneg := le_rfl, eq_trace := rfl, eq_spend := rfl, eq_defect := by simp },
    two_trans := fun c1 c2 => (show Slack2Cell _ _ from {
      delta := c1.delta + c2.delta,
      delta_nonneg := add_nonneg c1.delta_nonneg c2.delta_nonneg,
      eq_trace := c1.eq_trace.trans c2.eq_trace,
      eq_spend := c1.eq_spend.trans c2.eq_spend,
      eq_defect := by rw [c2.eq_defect, c1.eq_defect, add_assoc]
    }),
    two_antisymm := fun c1 c2 => by
      apply CertifiedMor.ext (A := A.toAssumptions)
      · exact c1.eq_trace
      · exact c1.eq_spend
      · have h1 := c1.eq_defect
        have h2 := c2.eq_defect
        rw [h1, add_assoc] at h2
        have hd1 : c1.delta = 0 := by linarith [c1.delta_nonneg, c2.delta_nonneg]
        rw [hd1, add_zero] at h1
        exact h1.symm,
    comp_monotone := fun {x y z} {f₁ f₂ g₁ g₂} hf hg =>
      let p₁ := chooseComp f₁ g₁
      let p₂ := chooseComp f₂ g₂
      have hp : p₁.1 = p₂.1 := by
        have h1 := p₁.2
        have h2 := p₂.2
        rw [hf.eq_trace, hg.eq_trace] at h1
        rw [h1] at h2
        injection h2
      { delta := hf.delta + hg.delta,
        delta_nonneg := add_nonneg hf.delta_nonneg hg.delta_nonneg,
        eq_trace := hp,
        eq_spend := by simp [compose, hf.eq_spend, hg.eq_spend],
        eq_defect := by
          simp [compose, hf.eq_defect, hg.eq_defect]
          linarith }
  }

/--
The Semantic Initial Property:
The tightest possible receipt (using exactly delta) is the initial object
in the poset of valid receipts for a given trace.
-/
theorem semantic_initial {S : System} {A : SegmentableAssumptions S} {X : Type v} {V : X → ℚ}
    {x y : X} (f : CertifiedMor S A.toAssumptions V x y) :
    ∃ (tight : CertifiedMor S A.toAssumptions V x y),
      tight.trace = f.trace ∧
      tight.spend = f.spend ∧
      tight.defect = max (delta S f.trace) (V y + f.spend - V x) ∧
      Nonempty (Slack2Cell tight f) := by
  let tight_defect := max (delta S f.trace) (V y + f.spend - V x)
  let tight : CertifiedMor S A.toAssumptions V x y := {
    trace := f.trace,
    spend := f.spend,
    defect := tight_defect,
    spend_nonneg := f.spend_nonneg,
    defect_nonneg := le_trans (delta_nonneg A.toAssumptions f.trace) (le_max_left _ _),
    law := by
      have h := le_max_right (delta S f.trace) (V y + f.spend - V x)
      linarith,
    defect_bound := le_max_left _ _
  }
  use tight
  refine ⟨rfl, rfl, rfl, ⟨?_⟩⟩
  exact {
    delta := f.defect - tight_defect,
    delta_nonneg := by
      have h1 := f.defect_bound
      have h2 : V y + f.spend - V x ≤ f.defect := by linarith [f.law]
      exact sub_nonneg.mpr (max_le h1 h2),
    eq_trace := rfl,
    eq_spend := rfl,
    eq_defect := (add_sub_cancel _ _).symm
  }

theorem certified_2category_exists
    (S : System) (A : SegmentableAssumptions S) (X : Type v) (V : X → ℚ)
    (chooseComp :
      ∀ {x y z : X}
        (f : CertifiedMor S A.toAssumptions V x y)
        (g : CertifiedMor S A.toAssumptions V y z),
        Σ' R₂₁ : S.Obs.V, S.Obs.comp g.trace f.trace = some R₂₁) :
    Nonempty (LocallyPosetal2Category.{v, 0} X) := by
  exact ⟨certified2Category S A X V chooseComp⟩

end Coh.V2
