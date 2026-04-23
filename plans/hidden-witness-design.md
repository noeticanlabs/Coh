# Hidden witness design for [`hiddenSystemFromV1`](../Coh/V2/FromV1.lean)

## Objective

Design the hidden carrier used by [`hiddenSystemFromV1`](../Coh/V2/FromV1.lean) so that the V1 operational layer in [`Coh/V1/Coh.lean`](../Coh/V1/Coh.lean) can discharge the V2 assumption fields in [`Coh.V2.Assumptions`](../Coh/V2/Axioms.lean:16).

The design must support:

- projection to a visible V1 trace
- hidden composition
- hidden cost
- nonempty fibers
- fiber decomposition
- identity zero cost
- additive or exactly compositional hidden cost

## Constraint from current V1 shim

Current V1 in [`Coh/V1/Coh.lean`](../Coh/V1/Coh.lean) exposes:

- visible traces via [`Coh.V1.Trace`](../Coh/V1/Coh.lean:38)
- visible concatenation via [`concat`](../Coh/V1/Coh.lean:62)
- acceptance via [`RVAccept`](../Coh/V1/Coh.lean:56)
- spend/defect summaries via [`traceSpend`](../Coh/V1/Coh.lean:42) and [`traceDefect`](../Coh/V1/Coh.lean:49)

It does **not** yet expose a genuine hidden execution object. Therefore the bridge must introduce one.

## Candidate designs

## Design A: certificate-carrying visible trace

Define hidden witnesses as a visible trace plus acceptance evidence.

Prototype shape:

- `structure V1Hidden (X : Type) where`
- `  trace : Coh.V1.Trace X`
- `  accepted : Coh.V1.RVAccept X trace`

### Projection

- [`projFromV1`](../Coh/V2/FromV1.lean) returns the underlying visible trace

### Hidden composition

- compose by visible [`concat`](../Coh/V1/Coh.lean:62)
- acceptance proof comes from [`rv_comp`](../Coh/V1/Coh.lean:74)

### Hidden cost

Choose one of:

- [`Coh.V1.traceSpend`](../Coh/V1/Coh.lean:42)
- [`Coh.V1.traceDefect`](../Coh/V1/Coh.lean:49)
- a pair-valued cost later projected to a scalar

### Pros

- easy fiber nonemptiness
- easy projection
- easy hidden composition

### Cons

- fibers become almost trivial, often singleton up to proof relevance
- semantic envelope may collapse to visible bookkeeping unless hidden cost differs from visible bookkeeping
- weaker as a model of the manuscript’s hidden/observable distinction

### Verdict

Good as the first implementation bridge if the goal is to get V2 instantiated quickly.

## Design B: proposal-history realizer witness

Define hidden witnesses as execution realizers that remember more than the visible trace, for example:

- source hidden representative
- target hidden representative
- history or proposal witness
- visible trace
- acceptance witness

Prototype shape:

- `structure V1Hidden (X : Type) where`
- `  srcHidden : ...`
- `  dstHidden : ...`
- `  hist : ...`
- `  trace : Coh.V1.Trace X`
- `  accepted : ...`

### Projection

- forget the extra hidden data and return the visible trace

### Hidden composition

- compose hidden endpoints/history witnesses together with visible [`concat`](../Coh/V1/Coh.lean:62)

### Hidden cost

- can be genuinely different from visible bookkeeping
- supports the manuscript’s semantic/visible separation more faithfully

### Pros

- matches the manuscript’s hidden-realization story in [`main.tex`](../coh-category-zenodo-final/paper/main.tex:449)
- gives nontrivial fibers
- makes semantic envelope meaningful rather than tautological

### Cons

- requires new hidden data structures not yet present in [`Coh/V1/Coh.lean`](../Coh/V1/Coh.lean)
- implementation burden is higher

### Verdict

This is the mathematically better final design.

## Design C: indexed hidden witness with explicit decomposition payload

Define hidden witnesses so composition data is part of the witness itself.

Prototype idea:

- hidden witness remembers its decomposition tree
- composition is structurally recursive on that tree
- projection forgets the tree and returns only the visible trace

### Pros

- makes [`fiber_decomp`](../Coh/V2/Axioms.lean:55) almost immediate
- makes [`hidden_cost_add`](../Coh/V2/Axioms.lean:46) natural by recursion

### Cons

- more abstract than current V1 operational presentation
- may be overengineered for the first bridge

### Verdict

Best if the long-term goal is a robust formal bridge with fewer later proof headaches.

## Recommended staged design

## Stage 1 implementation choice

Use **Design A** first in [`Coh/V2/FromV1.lean`](../Coh/V2/FromV1.lean):

- hidden witness = accepted visible trace
- projection = forget acceptance proof
- hidden cost = [`Coh.V1.traceDefect`](../Coh/V1/Coh.lean:49) or [`Coh.V1.traceSpend`](../Coh/V1/Coh.lean:42)

This is enough to instantiate V2 and test the bridge mechanics.

## Stage 2 mathematical upgrade

Then move toward **Design B** or **Design C** once the bridge compiles:

- add hidden endpoint/history/proposal data
- refine fibers from trivial proof wrappers to actual hidden realizers
- replace tautological nonemptiness/decomposition arguments with manuscript-faithful realizability theorems

## Exact recommendation for hidden cost

### Initial recommendation

Use [`Coh.V1.traceDefect`](../Coh/V1/Coh.lean:49) as the hidden cost in the first bridge.

Reason:

- it already plays the role of a conservative defect bound in [`Coh.V1.CohMor.valid`](../Coh/V1/Coh.lean:69)
- it aligns more naturally with [`Coh.V2.CertifiedMor.defect`](../Coh/V2/Certified.lean:17) and [`Coh.V2.delta`](../Coh/V2/Definitions.lean:21)

### Later upgrade

Once real hidden realizers exist, replace this with a true hidden execution cost distinct from visible bookkeeping.

## How each V2 assumption is supported by the design

- [`obs_assoc`](../Coh/V2/Axioms.lean:18): from visible trace composition
- [`obs_id_right`](../Coh/V2/Axioms.lean:26): from visible empty trace
- [`obs_id_left`](../Coh/V2/Axioms.lean:30): from visible empty trace
- [`fiber_nonempty`](../Coh/V2/Axioms.lean:34): hidden witness can be built from accepted trace data
- [`fiber_bounded`](../Coh/V2/Axioms.lean:38): bounded by chosen hidden-cost semantics
- [`id_fiber_zero`](../Coh/V2/Axioms.lean:42): empty accepted trace has zero cost
- [`hidden_cost_add`](../Coh/V2/Axioms.lean:46): induced from cost behavior of [`concat`](../Coh/V1/Coh.lean:62)
- [`fiber_decomp`](../Coh/V2/Axioms.lean:55): follows from composition structure on hidden witnesses, easiest in Design C, acceptable in Design A if hidden witnesses are just accepted traces

## Final recommendation

Implement [`hiddenSystemFromV1`](../Coh/V2/FromV1.lean) in two phases:

1. **Bridge-enabling phase:** hidden witness = accepted trace wrapper
2. **Semantic-faithful phase:** hidden witness = genuine realizer carrying extra hidden data beyond visible traces

This keeps the implementation path short while preserving a clear route to the stronger manuscript interpretation.
