# Final patch plan for [`coh-category-zenodo-final/paper/main.tex`](../coh-category-zenodo-final/paper/main.tex)

## Objective

Convert the V1-to-V2 continuity idea into concrete edits against [`main.tex`](../coh-category-zenodo-final/paper/main.tex) so the manuscript clearly presents V2 as the projection-aware completion of the V1 operational layer.

## Patch 1: Introduction framing paragraph

### Target location

Insert after the contribution list at [`main.tex:88-94`](../coh-category-zenodo-final/paper/main.tex:88).

### Edit goal

Introduce the two-layer story before any formal development begins.

### Planned content

Add one paragraph stating that:

- the trace/verifier/bookkeeping machinery is the operational base layer
- the hidden-realization, fiber, semantic-envelope, and categorical machinery is the abstract completion layer
- the second is built from the first rather than replacing it

## Patch 2: transition into Coh systems

### Target location

Insert between [`Concatenation`](../coh-category-zenodo-final/paper/main.tex:161) and [`Coh systems`](../coh-category-zenodo-final/paper/main.tex:169).

### Edit goal

Signal that the earlier trace algebra is the kernel that will now be reinterpreted through hidden/observable structure.

### Planned content

Add a short bridge paragraph explaining that the operational trace algebra will be lifted into a hidden-observable framework.

## Patch 3: admissible traces to morphisms bridge

### Target location

Insert after the admissible trace definition at [`main.tex:213-235`](../coh-category-zenodo-final/paper/main.tex:213).

### Edit goal

Prevent the later category section from reading like a new primitive arrow theory.

### Planned content

Add a remark stating that admissible traces are the operational source of the later morphism notion, and that certified morphisms are their abstract packaging.

## Patch 4: opening of The Coh category

### Target location

Insert before the hom-set definition at [`main.tex:279`](../coh-category-zenodo-final/paper/main.tex:279).

### Edit goal

Frame the category as closure of the earlier operational notion.

### Planned content

Add a short paragraph saying that the category is generated from admissible trace semantics rather than from a fresh arrow primitive.

## Patch 5: semantic cost section reframing

### Target location

Insert before [`Verifier-realizable hidden traces`](../coh-category-zenodo-final/paper/main.tex:449).

### Edit goal

Clarify that semantic cost is the projection-aware abstraction layer added on top of the operational bookkeeping layer.

### Planned content

Add a paragraph explaining that everything up to this point used only visible operational bookkeeping, and that the section now introduces hidden realizations and the envelope layer.

## Patch 6: strengthen Positioning and scope

### Target location

Expand [`main.tex:684-697`](../coh-category-zenodo-final/paper/main.tex:684).

### Edit goal

Make the continuity claim explicit in the part of the paper dedicated to interpretation and scope.

### Planned content

Add one strong paragraph of the form:

> The abstract projection-and-envelope layer is not a separate theory from the certified execution layer. The execution layer provides the operational law, while the projection-aware layer provides its semantic and categorical completion.

Add a displayed summary arrow if desired.

## Patch 7: conclusion refinement

### Target location

Insert after the boxed summary statements around [`main.tex:714-726`](../coh-category-zenodo-final/paper/main.tex:714).

### Edit goal

Leave the reader with the correct conceptual hierarchy.

### Planned content

Add a closing paragraph explicitly separating:

- operational certified trace layer
- projection-aware semantic and categorical layer

and stating that the latter completes the former.

## Patch 8: Lean 4 formalization sketch note

### Target location

Insert near the beginning of [`Lean 4 formalization sketch`](../coh-category-zenodo-final/paper/main.tex:730).

### Edit goal

Align the code architecture with the manuscript architecture.

### Planned content

Add a paragraph stating that the formalization should separate:

- a V1-style operational core for traces and verifier semantics
- a bridge layer that packages those semantics into the abstract V2 system signature
- analytic and categorical layers built from that packaged bridge

## Priority ordering

If only a small patch is acceptable, implement these first:

1. [`Introduction`](../coh-category-zenodo-final/paper/main.tex:73)
2. [`Semantic cost`](../coh-category-zenodo-final/paper/main.tex:447)
3. [`Positioning and scope`](../coh-category-zenodo-final/paper/main.tex:684)

If a full structural patch is acceptable, implement all eight insertions.

## Resulting narrative after patch

After these edits, the paper should read as follows:

- Sections on traces, admissibility, and verifier laws build the operational kernel
- The category section closes that operational kernel categorically
- The semantic cost section adds the projection-aware hidden layer
- The scope and conclusion sections explicitly state that this is a layered single theory rather than two separate frameworks
