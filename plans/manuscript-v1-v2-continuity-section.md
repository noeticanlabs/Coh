# Draft manuscript continuity section

## From V1 operational semantics to V2 categorical completion

Version 2 is not a separate theory from Version 1. Rather, it is the projection-aware abstract completion of the Version 1 certified transition framework.

In Version 1, the central objects are concrete execution traces, verifier acceptance, and the spend-defect transition law encoded at the level of certified transitions in [`coh-category-zenodo-final/code/Coh.lean`](../coh-category-zenodo-final/code/Coh.lean). That operational layer specifies what a certified transition system is: transitions carry executable trace content, costs accumulate along those traces, and certification is expressed by a verifier-governed inequality relating source value, target value, spend, and defect.

Version 2 keeps that operational content but reorganizes it into a projection-aware abstract framework. The key move is to separate hidden realizations from observable traces and to introduce a projection from hidden executions to visible behavior. This yields fibers of hidden witnesses over observable traces and, from those fibers, the envelope construction

\[
\delta(R) := \sup_{\xi \in \mathcal F_R} W(\xi),
\]

which captures the worst hidden cost compatible with an observable trace. Once this envelope is available, the concrete certified transitions of Version 1 can be repackaged as certified morphisms, and the composition laws inherited from the operational system become the categorical laws of the Version 2 certified category.

Accordingly, the relationship between the two versions is:

- Version 1 provides the operational kernel
- Version 2 provides the abstraction, envelope lift, and categorical closure of that kernel

This can be summarized as follows:

\[
\text{V1 operational core}
\longrightarrow
\text{hidden/observable reinterpretation}
\longrightarrow
\text{envelope construction}
\longrightarrow
\text{certified categorical completion.}
\]

Under this reading, Version 2 should not be understood as replacing Version 1. Instead, it explains the abstract structural consequences of Version 1. The operational notions of trace, verifier-realizable execution, spend, and defect in Version 1 lift respectively to the observable carrier, hidden witness structure, hidden cost semantics, envelope bound, and certified morphism machinery of Version 2.

In the Lean development, the same dependency story should hold. The Version 1 layer supplies the concrete execution boundary, while the Version 2 layer supplies the hidden-observable split, fiber construction, analytic envelope results, and locally preordered category. Thus the mathematical narrative and the code architecture coincide: Version 1 gives Coh its operational law, and Version 2 gives that law its projection-aware categorical completion.
