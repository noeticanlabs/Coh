# Last 20% Completion Plan: V1 → V2 → V3 in Lean

## Current State Analysis

| Piece | Status | Critical Gap |
|-------|--------|--------------|
| 1. δ Well-Defined | ⚠️ Partial | `rat_le_csSup`, `rat_csSup_le` are `sorry` stubs (Definitions.lean:17-18) |
| 2. Fiber Decomposition | ✅ Done | `fiber_decomp` in `Segmentable` structure, implemented in FiniteWord.lean |
| 3. Delta Subadditivity | ✅ Done | `delta_subadd` proven in Analytic.lean using pieces 1+2 |
| 4. Morphism Composition | ✅ Done | `compose_certified` in Certified.lean with `defect_bound` proof |
| 5. V3 Distance | ❌ Missing | No `def d` or `d_triangle` theorem |

---

## TODO: Execute in Order

### [ ] 1. Replace `sorry` stubs in Definitions.lean with proper ℚ supremum proofs

**File**: [`Coh/Coh/V2/Definitions.lean`](Coh/Coh/V2/Definitions.lean:17)

**Current (lines 17-18)**:
```lean
theorem rat_le_csSup {s : Set ℚ} {a : ℚ} (_bdd : BddAbove s) (_ha : a ∈ s) : a ≤ sSup s := sorry
theorem rat_csSup_le {s : Set ℚ} {a : ℚ} (_h : s.Nonempty) (_ha : ∀ x ∈ s, x ≤ a) : sSup s ≤ a := sorry
```

**Replace with**: Use `Finset` approximation since ℚ is dense. For any `a ∈ s`, `a ≤ sup s` by definition. For upper bound `a`, construct rational approximations.

**Result**: `δ(R)` becomes mathematically valid, not assumed.

---

### [ ] 2. Define V3 distance function `d`

**New file/module**: Add to `Coh/Coh/V2/Analytic.lean` or create `Coh/Coh/V2/Geometry.lean`

```lean
/-- V3 distance as infimum of delta over all traces -/
def d {S : System} (A : Assumptions S) (x y : S.Obs.V) : ℚ :=
  sInf { δ S τ | τ : Trace S x y }
```

**Note**: Need to properly define `Trace` type and prove `Nonempty` for the set.

---

### [ ] 3. Prove triangle inequality `d_triangle`

**Theorem**:
```lean
theorem d_triangle {S : System} (A : SegmentableAssumptions S)
    {x y z : S.Obs.V} :
    d A y z ≤ d A x y + d A x z := by
  -- Use infimum property: if τ₁ : x→y and τ₂ : x→z,
  -- then concatenated trace gives upper bound
  -- Use delta_subadd for the key inequality
```

**Key steps**:
1. Take arbitrary `ε > 0`
2. Find traces `τ₁ : x→y` and `τ₂ : x→z` with `δ S τ₁ < d x y + ε` and `δ S τ₂ < d x z + ε`
3. Use trace concatenation to form `τ = τ₁ ⊙ τ₂`
4. Apply `delta_subadd` to get `δ S τ ≤ δ S τ₁ + δ S τ₂`
5. Conclude by infimum property

---

### [ ] 4. Verify complete chain compiles

**Test**:
```bash
cd Coh && lake build
```

**Expected**: Zero `sorry` in the critical path for V1→V2→V3.

---

## What NOT to Do (Save Effort)

- ❌ Full GCCP formalization
- ❌ Perfect computable δ
- ❌ Full V1 module in Lean
- ❌ Performance optimizations
- ❌ Fancy tactics

---

## Verification Checklist

After completing:
- [ ] `rat_le_csSup` compiles without `sorry`
- [ ] `rat_csSup_le` compiles without `sorry`
- [ ] `delta_id` compiles (uses piece 1)
- [ ] `delta_subadd` compiles (uses pieces 1+2)
- [ ] `compose_certified` compiles (uses piece 3)
- [ ] `d_triangle` compiles (uses piece 3 + trace concatenation)
- [ ] `lake build` succeeds with zero `sorry` in critical path

---

## Result

$$\boxed{\text{Coh Category induces a verified quasi-metric geometry.}}$$