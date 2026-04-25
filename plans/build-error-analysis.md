# Build Error Analysis (Post-Mathlib Dependencies)

## Executive Summary

The `lake build` command now reveals pre-existing bugs that were hidden:

1. **Analytic.lean** - Real-specific lemma used incorrectly in `delta_add` proof
2. **FiniteWord.lean** - Multiple unsolved goals = hidden `sorry` holes
3. **No `sorry` in Category.lean** - The semantic_initial theorem is complete

## Build Errors

### Analytic.lean (Line 77)

```
error: could not unify the conclusion of `csSup_le h_non2`
  sSup (CostSet S R₂) ≤ ?m.132
with the goal
  sSup (CostSet S R₂) + S.Hid.cost ξ1 ≤ sSup (CostSet S R₂₁)
```

**Root Cause**: The proof uses `Real.le_sSup_add_sSup` incorrectly:
```lean
apply Real.le_sSup_add_sSup (CostSet S R₂) (CostSet S R₁) h2 h1
```

This lemma requires both sets already have elements that sum to within bounds, but the proof structure doesn't establish this correctly.

**Fix Required**: Rewrite the second direction of `delta_add` with explicit bounding arguments.

### FiniteWord.lean (Multiple)

```
error: unsolved goals
- head :: List.map (Prod.fst ∘ fun a => (a, b)) tail = head :: tail
- (List.map ?m.297 ξ).length = List.length R
- List.take n (List.map Prod.fst ξ) = R₂
- List.drop n (List.map Prod.fst ξ) = R₁
```

**Root Cause**: The `fiber_decomp` proof has 4 incomplete proof branches = 4 hidden `sorry` holes.

**Fix Required**: Complete the structural decomposition proofs.

## Impact on ℝ→ℚ Change

Before making the ℝ→ℚ change, these build errors MUST be fixed first because:

1. The codebase doesn't compile - changes would mask the real issues
2. The Real-specific lemmas in Analytic.lean need rewriting anyway
3. The structural issues in FiniteWord.lean are foundational

## Plan

1. [ ] Fix Analytic.lean `delta_add` proof (Real-specific lemma)
2. [ ] Fix FiniteWord.lean `fiber_decomp` proof (4 branches)
3. [ ] Verify clean build
4. [ ] Then proceed with ℝ→ℚ replacement

## Files That Need Changes

| File | Lines | Issue |
|------|-------|-------|
| Analytic.lean | 68-88 | `delta_add` proof uses Real lemma incorrectly |
| FiniteWord.lean | 85-150 | `fiber_decomp` = 4 incomplete branches |

## Note on User's Original Directives

The user's three directives:
1. ℝ → ℚ: Can't proceed (build broken)
2. Import change: Can't proceed (build broken)  
3. Close `sorry`: Actually there are 4+ hidden `sorry` in FiniteWord.lean

The foundation is not ready for Navier-Stokes Caelus until build errors are fixed.