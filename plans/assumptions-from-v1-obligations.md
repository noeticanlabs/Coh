# Theorem obligations for [`assumptionsFromV1`](../Coh/V2/FromV1.lean)

## Goal

[`assumptionsFromV1`](../Coh/V2/FromV1.lean) should be the V1-induced instance of [`Coh.V2.Assumptions`](../Coh/V2/Axioms.lean:16) for the system packaged by [`systemFromV1`](../Coh/V2/FromV1.lean).

This file records the exact obligations that must be discharged to construct that instance.

## Master target

Construct:

- [`assumptionsFromV1`](../Coh/V2/FromV1.lean) : [`Coh.V2.Assumptions`](../Coh/V2/Axioms.lean:16) [`systemFromV1`](../Coh/V2/FromV1.lean)

where [`systemFromV1`](../Coh/V2/FromV1.lean) is the V1-instantiated [`Coh.V2.System`](../Coh/V2/Primitive.lean:20).

## Obligation 1: observable associativity

### Target field

- [`Coh.V2.Assumptions.obs_assoc`](../Coh/V2/Axioms.lean:18)

### Required statement shape

For V1-derived observable traces `R₁`, `R₂`, `R₃`, if:

- [`Obs.comp`](../Coh/V2/Primitive.lean:16) `R₂ R₁ = some R₁₂`
- [`Obs.comp`](../Coh/V2/Primitive.lean:16) `R₃ R₂ = some R₂₃`
- [`Obs.comp`](../Coh/V2/Primitive.lean:16) `R₃ R₁₂ = some R₁₂₃`

then:

- [`Obs.comp`](../Coh/V2/Primitive.lean:16) `R₂₃ R₁ = some R₁₂₃`

### V1 source

This must come from the associativity of V1 trace concatenation built from [`concat`](../Coh/V1/Coh.lean:62), after [`Coh.V1.Trace`](../Coh/V1/Coh.lean:38) is stabilized enough to support composition on endpoints.

### Implementation note

This is the first place where endpoint-indexed traces or equivalent source-target data become mandatory.

## Obligation 2: observable right identity

### Target field

- [`Coh.V2.Assumptions.obs_id_right`](../Coh/V2/Axioms.lean:26)

### Required statement shape

For every observable trace `R`:

- [`Obs.comp`](../Coh/V2/Primitive.lean:16) `R Obs.id = some R`

### V1 source

This should be induced by the interaction between [`emptyTrace`](../Coh/V1/Coh.lean:58) and [`concat`](../Coh/V1/Coh.lean:62).

## Obligation 3: observable left identity

### Target field

- [`Coh.V2.Assumptions.obs_id_left`](../Coh/V2/Axioms.lean:30)

### Required statement shape

For every observable trace `R`:

- [`Obs.comp`](../Coh/V2/Primitive.lean:16) `Obs.id R = some R`

### V1 source

Again induced from [`emptyTrace`](../Coh/V1/Coh.lean:58) and [`concat`](../Coh/V1/Coh.lean:62).

## Obligation 4: fiber nonemptiness

### Target field

- [`Coh.V2.Assumptions.fiber_nonempty`](../Coh/V2/Axioms.lean:34)

### Required statement shape

For every observable trace `R`, the V2 fiber [`Coh.V2.Fiber`](../Coh/V2/Definitions.lean:13) over `R` is nonempty.

### V1 source

This means the bridge must define the hidden witness carrier so that every observable V1 trace has at least one hidden representative.

### Design fork

- **Free witness design:** hidden witnesses are pairs of a trace together with certification data, making nonemptiness tautological
- **Realizer design:** hidden witnesses are genuine verifier-realizing executions, in which case nonemptiness requires a V1 realizability theorem or axiom

## Obligation 5: fiber boundedness

### Target field

- [`Coh.V2.Assumptions.fiber_bounded`](../Coh/V2/Axioms.lean:38)

### Required statement shape

For every observable trace `R`, the cost set [`Coh.V2.CostSet`](../Coh/V2/Definitions.lean:17) is bounded above.

### V1 source

This must come from a chosen hidden cost model derived from V1 spend, V1 defect, or another explicit hidden execution cost.

### Minimal route

If hidden cost is defined by a V1 bounded quantity such as [`Coh.V1.traceDefect`](../Coh/V1/Coh.lean:49), boundedness can be discharged by choosing that quantity itself as an upper bound.

## Obligation 6: identity fiber zero cost

### Target field

- [`Coh.V2.Assumptions.id_fiber_zero`](../Coh/V2/Axioms.lean:42)

### Required statement shape

Every hidden witness projecting to the observable identity has hidden cost `0`.

### V1 source

This must come from the V1 operational identity trace [`emptyTrace`](../Coh/V1/Coh.lean:58) together with the chosen hidden cost function.

### Minimal route

Define hidden cost so the hidden witness of the empty trace has cost zero by construction.

## Obligation 7: hidden cost additivity

### Target field

- [`Coh.V2.Assumptions.hidden_cost_add`](../Coh/V2/Axioms.lean:46)

### Required statement shape

Whenever hidden witness composition is defined, the hidden cost of the composite is the sum of the hidden costs.

### V1 source

This should be induced by the additive behavior of [`Coh.V1.traceSpend`](../Coh/V1/Coh.lean:42), [`Coh.V1.traceDefect`](../Coh/V1/Coh.lean:49), or another chosen hidden cost semantics over [`concat`](../Coh/V1/Coh.lean:62).

### Key choice

You must decide whether hidden cost tracks:

- syntactic spend
- syntactic defect
- a new hidden execution cost extracted from verifier realizers

That choice determines the proof shape of this field and the later meaning of [`Coh.V2.delta`](../Coh/V2/Definitions.lean:21).

## Obligation 8: fiber decomposition

### Target field

- [`Coh.V2.Assumptions.fiber_decomp`](../Coh/V2/Axioms.lean:55)

### Required statement shape

Any hidden witness of a composite observable trace must decompose into hidden witnesses for the component observable traces.

### V1 source

This must come from a decomposition theorem for verifier-realizing V1 hidden executions compatible with observable concatenation from [`concat`](../Coh/V1/Coh.lean:62).

### This is the hardest obligation

Among all fields of [`Coh.V2.Assumptions`](../Coh/V2/Axioms.lean:16), this is the most structurally demanding.

If the hidden witness carrier is chosen too weakly, this field becomes impossible or vacuous. The bridge design should therefore make hidden witnesses explicitly compositional.

## Recommended proof staging

1. First discharge the observable laws:
   - [`obs_id_right`](../Coh/V2/Axioms.lean:26)
   - [`obs_id_left`](../Coh/V2/Axioms.lean:30)
   - [`obs_assoc`](../Coh/V2/Axioms.lean:18)
2. Next fix the hidden witness model and hidden cost semantics
3. Then discharge:
   - [`fiber_nonempty`](../Coh/V2/Axioms.lean:34)
   - [`fiber_bounded`](../Coh/V2/Axioms.lean:38)
   - [`id_fiber_zero`](../Coh/V2/Axioms.lean:42)
   - [`hidden_cost_add`](../Coh/V2/Axioms.lean:46)
4. Leave [`fiber_decomp`](../Coh/V2/Axioms.lean:55) last, since it depends on the full hidden witness design

## Minimal acceptance criteria

The bridge is mature enough to support downstream V2 development once [`assumptionsFromV1`](../Coh/V2/FromV1.lean) can be stated with explicit placeholders for all eight fields and the source of each field is documented against V1 primitives.
