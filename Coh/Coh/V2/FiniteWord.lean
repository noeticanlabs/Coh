import Coh.V2.Primitive
import Coh.V2.Definitions
import Coh.V2.Axioms
import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith

/-!
## Coh V2 Finite-Word Model (Rational Version)

This module implements a concrete Coh V2 system based on finite alphabets
and list-based traces using strictly rational defect envelopes.
-/

namespace Coh.V2.FiniteWord

/-- The set of hidden traces (pairs of observable and hidden symbols). -/
def HiddenG (A B : Type) : Type := List (A × B)
/-- The set of observable traces (lists of observable symbols). -/
def ObservableV (A : Type) : Type := List A

/-- Projection from hidden to observable layer by dropping hidden tags. -/
def proj {A B : Type} (ξ : HiddenG A B) : ObservableV A := ξ.map Prod.fst

/-- Exact cost of a hidden trace, summed over hidden tags. -/
def hiddenCost (A B : Type) (c_B : B → ℚ) (ξ : HiddenG A B) : ℚ :=
  (ξ.map (fun p => c_B p.2)).sum

/-- The maximum cost of a single hidden symbol. -/
def c_max {B : Type} [Fintype B] [Nonempty B] (c_B : B → ℚ) : ℚ :=
  (Finset.univ.image c_B).max' (by simp [Finset.image_nonempty, Finset.univ_nonempty])

/-- Projection distributes over mapping. -/
theorem proj_map_id {A B : Type} (R : ObservableV A) (b : B) :
    @proj A B (R.map (fun a => (a, b))) = R := by
  induction R with
  | nil => rfl
  | cons hd tl ih =>
      show @proj A B ((hd :: tl).map (fun a => (a, b))) = hd :: tl
      have h1 : (hd :: tl).map (fun a => (a, b)) = (hd, b) :: tl.map (fun a => (a, b)) := rfl
      have h2 : @proj A B ((hd, b) :: tl.map (fun a => (a, b))) = hd :: @proj A B (tl.map (fun a => (a, b))) := rfl
      have h3 : @proj A B (tl.map (fun a => (a, b))) = tl := ih
      rw [h1, h2, h3]

/-- Hidden length equals observable length (1:1 alignment). -/
theorem proj_length {A B : Type} (ξ : HiddenG A B) : (proj ξ).length = ξ.length := by
  simp [proj, List.length_map]

/-- Cost of a hidden trace is bounded by its length and max symbol cost. -/
theorem cost_bound {A B : Type} [Fintype B] [Nonempty B] (c_B : B → ℚ) (ξ : HiddenG A B) :
    hiddenCost A B c_B ξ ≤ (ξ.length : ℚ) * c_max c_B := by
  induction ξ with
  | nil => simp [hiddenCost]
  | cons p rest ih =>
    have hmax : c_B p.2 ≤ c_max c_B := by exact Finset.le_max' _ _ (Finset.mem_image_of_mem c_B (Finset.mem_univ _))
    calc
      hiddenCost A B c_B (p :: rest) = c_B p.2 + hiddenCost A B c_B rest := rfl
      _ ≤ c_max c_B + (rest.length : ℚ) * c_max c_B := add_le_add hmax ih
      _ = (rest.length : ℚ) * c_max c_B + c_max c_B := by rw [add_comm]
      _ = ((rest.length : ℚ) + 1) * c_max c_B := by rw [add_mul, one_mul]
      _ = ((p :: rest).length : ℚ) * c_max c_B := by simp

/-- Hidden composition is list concatenation. -/
def hComp {A B : Type} (x1 x2 : HiddenG A B) : Option (HiddenG A B) := some (List.append x1 x2)
/-- Observable composition is list concatenation. -/
def oComp {A : Type} (r1 r2 : ObservableV A) : Option (ObservableV A) := some (List.append r1 r2)

/-- The null observable trace. -/
def obsId {A : Type} : ObservableV A := []

/-- Hidden system for words. -/
def hiddenSystem (A B : Type) (c_B : B → ℚ) : HiddenSystem where
  G := HiddenG A B; comp := hComp; cost := hiddenCost A B c_B

/-- Observable system for words. -/
def observableSystem (A : Type) : ObservableSystem where
  V := ObservableV A; comp := oComp; id := obsId; complexity := fun _ => 0

/-- Sealed rational system for words. -/
def system (A B : Type) [Fintype B] [Nonempty B] (c_B : B → ℚ) : System where
  Hid := hiddenSystem A B c_B
  Obs := observableSystem A
  proj := @proj A B
  proj_comp := by
    intros ξ₂ ξ₁ ξ h
    have h_hcomp : hComp ξ₂ ξ₁ = some ξ := h
    simp [hComp] at h_hcomp
    injection h_hcomp with h_eq
    subst h_eq
    simp [proj, observableSystem, oComp, List.map_append]
  delta := fun R => (R.length : ℚ) * c_max c_B

/-- Typeclass requiring at least one positive-cost hidden symbol. -/
class HasPositiveCost (B : Type) [Fintype B] (c_B : B → ℚ) : Prop where
  exists_pos : ∃ b : B, c_B b > 0

/-- Typeclass requiring that all hidden symbols have non-negative cost. -/
class HasNonnegativeCost (B : Type) (c_B : B → ℚ) : Prop where
  nonneg : ∀ b, 0 ≤ c_B b

/-- Assumptions implementation for FiniteWord (Rational-Only). -/
def assumptions (A B : Type) [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Nonempty A] [Nonempty B] (c_B : B → ℚ) [hp : HasPositiveCost B c_B] [hn : HasNonnegativeCost B c_B] :
    Assumptions (system A B c_B) :=
{ obs_assoc := by
    intros R1 R2 R3 R12 R23 R123 h12 h23 h123a
    simp [system, observableSystem, oComp] at h12 h23 h123a
    cases h12; cases h23; cases h123a
    simp [system, observableSystem, oComp, List.append_assoc]
  obs_id_right := fun R => by
    simp [system, observableSystem, oComp, obsId]
  obs_id_left := fun R => by
    simp [system, observableSystem, oComp, obsId]
  fiber_nonempty := by
    intros R
    let b : B := Classical.choice (show Nonempty B from inferInstance)
    refine ⟨R.map (fun a => (a, b)), ?_⟩
    change proj (R.map (fun a => (a, b))) = R
    induction R with
    | nil => rfl
    | cons hd tl ih =>
        rw [show (hd :: tl).map (fun a => (a, b)) = (hd, b) :: tl.map (fun a => (a, b)) by rfl,
            show proj ((hd, b) :: tl.map (fun a => (a, b))) = hd :: proj (tl.map (fun a => (a, b))) by rfl,
            proj_map_id]
  delta_le := by
    intros R ξ hξ
    simp [Fiber] at hξ
    have hproj : proj ξ = R := hξ
    have hlen : ξ.length = R.length := by rw [← proj_length ξ, hproj]
    have hcost := cost_bound c_B ξ
    dsimp [system]
    rw [← hlen]
    exact hcost
  delta_id := by simp [system, observableSystem, obsId, zero_mul]


  id_fiber_zero := by
    intros ξ hξ
    simp [Fiber] at hξ
    have hproj : proj ξ = [] := hξ
    have hlen : ξ.length = 0 := by
      simpa [proj_length ξ] using congrArg List.length hproj
    cases ξ with
    | nil => rfl
    | cons hd tl => cases hlen
  hidden_cost_add := by
    intros ξ₂ ξ₁ ξ h
    simp [system, hiddenSystem, hComp] at h
    cases h
    simp [system, hiddenSystem, hiddenCost, List.map_append, List.sum_append]
  cost_nonneg := by
    intros ξ
    induction ξ with
    | nil => rfl
    | cons p rest ih =>
      simp [system, hiddenSystem, hiddenCost]
      exact add_nonneg (hn.nonneg p.2) ih
  delta_nonneg := by
    intros R
    dsimp [system]
    apply mul_nonneg
    · simp
    · have b : B := Classical.choice (show Nonempty B from inferInstance)
      have h_max : c_B b ≤ c_max c_B := Finset.le_max' _ _ (Finset.mem_image_of_mem c_B (Finset.mem_univ _))
      exact (hn.nonneg b).trans h_max
  delta_subadd := by
    intros R1 R2 R21 hc
    simp [system, observableSystem, oComp] at hc
    cases hc
    simp [system, List.length_append, Nat.cast_add, add_mul]

  structural_independence := by
    rcases hp.exists_pos with ⟨b, hb⟩
    let a : A := Classical.choice (show Nonempty A from inferInstance)
    let R : ObservableV A := [a]
    use R
    dsimp [system]
    simp [R]
    have h_cmax : c_max c_B ≥ c_B b := Finset.le_max' _ _ (Finset.mem_image_of_mem c_B (Finset.mem_univ _))
    exact lt_of_lt_of_le hb h_cmax
  comp_reachable := fun {R1 R2 R3 Ra Rb} _ _ => ⟨List.append Rb Ra, rfl⟩ }

/-- FiniteWord systems are segmentable. -/
def segmentable (A B : Type) [Fintype B] [Nonempty B] (c_B : B → ℚ) : Segmentable (system A B c_B) where
  fiber_decomp := by
    intros R₁ R₂ R₂₁ ξ hc hξ
    simp [system, observableSystem, oComp] at hc
    cases hc
    simp [Fiber] at hξ
    have hproj : proj ξ = List.append R₂ R₁ := hξ
    let n := R₂.length
    use ξ.take n, ξ.drop n
    constructor
    · simp [system, hiddenSystem, hComp, List.take_append_drop]
    · constructor
      · show proj (ξ.take n) = R₂
        have htake : List.take n (proj ξ) = List.take n (List.append R₂ R₁) := by
          rw [hproj]
        rw [show proj (ξ.take n) = List.take n (proj ξ) by simp [proj]]
        rw [htake]
        simp [n]
      · show proj (ξ.drop n) = R₁
        have hdrop : List.drop n (proj ξ) = List.drop n (List.append R₂ R₁) := by
          rw [hproj]
        rw [show proj (ξ.drop n) = List.drop n (proj ξ) by simp [proj]]
        rw [hdrop]
        simp [n]

def segmentableAssumptions (A B : Type) [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Nonempty A] [Nonempty B] (c_B : B → ℚ) [hp : HasPositiveCost B c_B] [hn : HasNonnegativeCost B c_B] :
    SegmentableAssumptions (system A B c_B) :=
{ toAssumptions := assumptions A B c_B
  toSegmentable := segmentable A B c_B }

/-- Constructor for a finite word system with its verified assumptions. -/
def mkFiniteWordSystem
    (A B : Type) [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Nonempty A] [Nonempty B] (c_B : B → ℚ) [hp : HasPositiveCost B c_B] [hn : HasNonnegativeCost B c_B] : VerifiedSystem :=
  ⟨system A B c_B, assumptions A B c_B⟩

end Coh.V2.FiniteWord
