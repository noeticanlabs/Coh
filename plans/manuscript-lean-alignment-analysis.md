# Manuscript-to-Lean Alignment Analysis

## Overview

This document compares the provided V2 LaTeX manuscript to the existing Lean V2 codebase and identifies alignment gaps.

## Manuscript Structure

| Section | Lean Module | Status |
|---------|-------------|--------|
| 02_primitive.tex | Primitive.lean | ✓ ALIGNED |
| 03_definitions.tex | Definitions.lean | ✓ ALIGNED |
| 04_axioms.tex | Axioms.lean | ✓ ALIGNED |
| 05_analytic.tex | Analytic.lean | ✓ ALIGNED |
| 06_certified.tex | Certified.lean | ✓ ALIGNED |
| 07_category.tex | Category.lean | ✓ ALIGNED |
| 08_diagram.tex | — | Documentation only |
| 09_example.tex | — | **MISSING** |
| 10_conclusion.tex | — | Documentation only |
| appendix_lean_map.tex | — | Out of date |

## Detailed Correspondence

### Analytic Theorems (Section 05)

| Manuscript | Lean | Status |
|------------|------|--------|
| lem:envelope_soundness | envelope_soundness | ✓ Exact match |
| lem:envelope_minimality | envelope_minimality | ✓ Exact match |
| lem:delta_id | delta_id | ✓ Exact match |
| lem:pointwise_composite_bound | pointwise_composite_bound | ✓ Exact match |
| thm:delta_subadd | delta_subadd | ✓ Exact match |

### Categorical Theorems (Sections 06-07)

| Manuscript | Lean | Status |
|------------|------|--------|
| def:certified_morphism | CertifiedMor | ✓ Exact match |
| def:id_certified | idMor | ✓ Exact match |
| lem:id_certified | id_certified | ✓ Exact match |
| def:compose_certified | compose | ✓ Exact match |
| lem:compose_certified | compose_certified | ✓ Exact match |
| thm:assoc_certified | assoc_certified | ✓ Exact match |
| thm:identity_laws | id_right_certified, id_left_certified | ✓ Split but aligned |
| def:hom_preorder | HomLE | ✓ Exact match |
| lem:hom_preorder | instHomPartialOrder | ✓ Implemented as instance |
| thm:compose_monotone | comp_monotone (in LocalPreorderCategory) | ✓ In structure |
| thm:certified_category | certified_category | ✓ Exact match |

### Additional Lean-Only Content

The Lean codebase contains several items not explicitly in the manuscript:

1. **Model.lean** — Trivial model existence proof (theorem: trivial_category_exists)
2. **BridgeLemmas.lean** — Trace-level lemmas (traceSpend_concat, traceDefect_concat)
3. **FromV1.lean, FromV1Degenerate.lean, FromV1Quotient.lean** — V1→V2 bridges

---

## Identified Gaps

### GAP 1: Missing Concrete Example (Section 09)

**Severity: HIGH**

The manuscript section 09_example.tex provides a finite-word model instantiation. This is **not present** in the Lean codebase.

Required additions:
- Create `Coh/V2/FiniteWord.lean` (or similar)
- Define hidden alphabet Σ = A × B
- Define observable alphabet A
- Define projection by erasing B-coordinate
- Define additive hidden cost function
- Prove all 7 axioms hold for this model
- Prove tight subadditivity lemma

### GAP 2: Out-of-Date Appendix Mapping

**Severity: LOW**

The appendix_lean_map.tex references should be verified against current Lean file locations. Current Lean files are in:
- `Coh/Coh/V2/` (not `Coh/V2/` as manuscript may imply)

### GAP 3: No Explicit "HomLE as Preorder" Theorem

**Severity: LOW (cosmetic)**

The manuscript defines `def:hom_preorder` and `lem:hom_preorder` separately. In Lean, this is implemented as `instHomPartialOrder` instance. Functionally equivalent but may confuse readers expecting exact theorem names.

### GAP 4: Diagram Section Not Formalized

**Severity: NONE (documentation only)**

Section 08_diagram.tex contains TikZ visualizations. These are not meant to be formalized.

---

## Summary

| Category | Count |
|----------|-------|
| Perfect alignment | 15 |
| Cosmetic differences | 2 |
| Missing content | 1 |
| Documentation only | 2 |

**Overall: The manuscript and Lean codebase are well-aligned. The primary gap is the missing concrete finite-word example in Lean.**

---

## Recommended Next Steps

1. [ ] Create `Coh/Coh/V2/FiniteWord.lean` with the example model
2. [ ] Verify axiom satisfaction proofs match manuscript lemmas
3. [ ] Update appendix reference paths if needed
4. [ ] Consider adding explicit `hom_preorder` theorem for clarity (optional)