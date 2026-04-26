# Last 20% - Lean Closure Plan

## Current Status

| Issue | Location | Count |
|-------|----------|-------|
| `sorry` | V1/Coh.lean | 2 |
| `sorry` | V2/Definitions.lean | 3 |
| `sorry` | V2/FiniteWord.lean | 1 |
| **Total sorry** | | **6** |
| Non-computing SupSet ℚ | Definitions.lean | 1 |
| ℚ supremum layer | All analytic proofs | FAKE |

---

## Phase 1 — Remove Mathematically False Layer (PRIORITY)

### ❌ Remove:
```lean
noncomputable instance : SupSet ℚ := ⟨fun _ => 0⟩  -- REMOVE

theorem rat_le_csSup ... := sorry  -- REMOVE  
theorem rat_csSup_le ... := sorry  -- REMOVE
```

### ✅ Replace with:
```lean
-- Keep costs in ℚ (verifier layer)
def CostSetQ (S : System) (R : S.Obs.V) : Set ℚ := ...

-- Move envelope to ℝ (analytic layer)
def CostSetReal (S : System) (R : S.Obs.V) : Set ℝ :=
  { x : ℝ | ∃ c : ℚ, c ∈ CostSetQ S R ∧ x = (c : ℝ) }

def delta (S : System) (R : S.Obs.V) : ℝ :=
  sSup (CostSetReal S R)
```

---

## Phase 2 — Rebuild Analytic Stack

### Required Lemma Stack:

```lean
-- If fiber is nonempty, real cost set is nonempty
lemma costset_real_nonempty
    {S : System} {R : S.Obs.V}
    (hne : FiberNonempty S R) :
    (CostSetReal S R).Nonempty := ...

-- If fiber is bounded in ℚ, real cost set is bounded above  
lemma costset_real_bddAbove
    {S : System} {R : S.Obs.V}
    (hb : FiberBoundedQ S R) :
    BddAbove (CostSetReal S R) := ...

-- Every hidden cost ≤ delta
theorem envelope_sound
    {S : System} {R : S.Obs.V} {ξ : S.Hid.G}
    (hb : BddAbove (CostSetReal S R))
    (hξ : ξ ∈ Fiber S R) :
    (S.Hid.cost ξ : ℝ) ≤ delta S R := ...

-- Delta is minimal sound bound
theorem envelope_minimal
    {S : System} {R : S.Obs.V} {Δ : ℝ}
    (hne : (CostSetReal S R).Nonempty)
    (hΔ : ∀ ξ : S.Hid.G, ξ ∈ Fiber S R → (S.Hid.cost ξ : ℝ) ≤ Δ) :
    delta S R ≤ Δ := ...

-- Delta at identity is zero
theorem delta_id
    {S : System} {e : S.Obs.V}
    (hid : IdentityFiberZero S e) :
    delta S e = 0 := ...

-- THE CORE THEOREM (Layer 2)
theorem delta_subadd
    {S : System}
    (hseg : Segmentable S)
    (hcost : CostAdditive S)
    {R₁ R₂ R₂₁ : S.Obs.V}
    (hc : S.Obs.comp R₂ R₁ = some R₂₁)
    (hb₁ : FiberBoundedQ S R₁)
    (hb₂ : FiberBoundedQ S R₂) :
    delta S R₂₁ ≤ delta S R₁ + delta S R₂ := ...
```

---

## Phase 3 — Fix Remaining sorrys

### V1/Coh.lean (2):
```lean
-- Add nonnegativity proofs to Step structure:
structure Step (X : Type) where
  src : X
  dst : X
  glyph : Glyph
  costSpend : ℚ
  costDefect : ℚ
  spend_nonneg : 0 ≤ costSpend  -- NEW FIELD
  defect_nonneg : 0 ≤ costDefect  -- NEW FIELD
  typed : Prop
  compiles_ok : Glyph.compiles glyph
```

### FiniteWord.lean (1):
```lean
-- Add HasNonnegativeCost class:
class HasNonnegativeCost (B : Type) (c_B : B → ℚ) : Prop where
  nonneg : ∀ b, 0 ≤ c_B b

-- Then prove:
theorem cost_nonneg := ...
```

---

## Phase 4 — Patch Certified Morphisms

Change `defect_bound` to use ℝ cast:
```lean
defect_bound : delta S trace ≤ (defect : ℝ)
```

---

## Phase 5 — Add V3 Distance

```lean
def d (x y : X) := sInf { delta S τ | τ : Trace x y }

theorem d_triangle : d x z ≤ d x y + d y z := ...
```

---

## Priority Order Summary

```
Phase 1: Remove fake SupSet ℚ / move delta to ℝ  ← START HERE
Phase 2: Rebuild analytic lemma stack
Phase 3: Remove remaining 6 sorrys  
Phase 4: Patch certified morphisms
Phase 5: Add V3
```

---

## Files To Modify

1. `Coh/V2/Definitions.lean` - Core definitions
2. `Coh/V2/Axioms.lean` - References to CostSetQ
3. `Coh/V2/Analytic.lean` - Proofs
4. `Coh/V2/Certified.lean` - Defect bounds
5. `Coh/V1/Coh.lean` - Step structure
6. `Coh/V2/FiniteWord.lean` - Nonnegativity

---

## Success Criteria

After all phases:
- 0 `sorry` in core formalization
- `delta : ℝ` not ℚ  
- `delta_subadd` compiles cleanly
- V3 distance defined