# Coh Simulation Design

## Overview
This document designs an effective simulation to showcase the Coh categorical computation framework. The simulation demonstrates the core concepts: hidden vs observable layers, delta (defect envelope), and certified morphisms.

## Core Concepts Demonstrated

### 1. Hidden vs Observable Layers
- **Hidden Layer**: Internal computation traces with actual costs
- **Observable Layer**: External behavior visible to adversary
- **Projection**: Maps hidden traces to observable traces

### 2. Key Invariant: The Coh Inequality
```
V(y) + spend ≤ V(x) + defect
```
Where:
- `V`: Potential function (valuation)
- `spend`: Hidden cost
- `defect`: Bounded by delta

### 3. Delta (Defect Envelope)
The tightest possible defect bound for a given observable trace R:
```
delta(R) = sSup { cost(ξ) | ξ ∈ Fiber(R) }
```

## Simulation Options

### Option A: Interactive Console Simulation
**Best for**: Live demonstration, tutorials

```
┌─────────────────────────────────────────────────────┐
│  COH SIMULATION: Secure Computation Protocol        │
├─────────────────────────────────────────────────────┤
│                                                     │
│  Hidden Layer          Observable Layer              │
│  ┌───────────┐         ┌───────────┐                 │
│  │ ξ₁: [a,X] │ ──────▶ │ R₁: [a]  │                 │
│  │ cost: 2.0  │         │          │                 │
│  └───────────┘         └───────────┘                 │
│       │                                            │
│       │ compose                                    │
│       ▼                                            │
│  ┌───────────┐                                      │
│  │ ξ₂: [b,Y] │ ──────▶ R₂: [b]                     │
│  │ cost: 1.5 │                                      │
│  └───────────┘                                      │
│                                                     │
│  COMPOSITE: R₁++R₂ → [a,b]                          │
│  Hidden: ξ₁++ξ₂ = [a,X,b,Y]                         │
│  Total Cost: 3.5                                    │
│  Delta([a,b]): ≤ 3.5  (subadditivity)               │
│                                                     │
│  VERIFIED: 2.5 + 1.5 ≤ 3.0 + 2.0 ✓                  │
│                                                     │
└─────────────────────────────────────────────────────┘
```

### Option B: Visual Diagram with Cost Flow
**Best for**: Papers, presentations

Shows:
1. Hidden traces with costs
2. Projection to observable
3. Delta envelope
4. Composition and cost additivity

### Option C: Test-Driven Visualization
**Best for**: Validating the math

```lean
-- Simulation test that users can run
#check simulate_two_morphisms
#check verify_coh_inequality
#check demo_delta_subadditivity
```

## Recommended Implementation

### 1. Console Simulation (`Simulation.lean`)
A Lean REPL-based simulation showing:
- Creating morphisms with traces and costs
- Composing morphisms
- Computing delta bounds
- Verifying the Coh inequality

### 2. Python/JavaScript Visualization
For interactive web-based demonstration:
- Step-by-step trace construction
- Cost calculation
- Delta visualization
- Composition verification

### 3. ASCII Diagram Generator
Simple text-based output showing the flow

## Implementation Plan

1. **Create `Simulation.lean`**: Lean module with simulation functions
2. **Add test cases**: Demonstrate key properties
3. **Create visualization script**: Python/JS for diagrams
4. **Document with examples**: Show the inequality, delta, etc.

## Key Examples to Simulate

### Example 1: Basic Two-State System
```
States: x, y
Alphabet: {a, b}
Hidden costs: cost(a→X) = 2, cost(b→Y) = 1.5

Morphisms:
- f: x → y via 'a' with spend=2
- g: y → z via 'b' with spend=1.5

Verify: V(z) + 3.5 ≤ V(x) + delta(ab)
```

### Example 2: Delta Subadditivity
```
delta([a,b]) ≤ delta([a]) + delta([b])
```
Show that the envelope is subadditive.

### Example 3: Structural Independence
Show a trace with positive delta proving the penalty cannot be zeroed out.