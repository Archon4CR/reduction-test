# ReductionTest — Reduction Proof Testing Project

This project uses the Archon automated theorem proving framework and the ComplexityReduction library to complete Lean 4 formalized proofs of 3 NP-completeness reduction problems. All proofs have 0 sorry and are axiom-clean (depending only on propext, Classical.choice, Quot.sound); lake build is green.

## Proof Overview

| File | Reduction | CR Reuse Strategy |
|------|------|-------------|
| ReductionTest/NAE3SAT.lean | 3SAT -> NAE-3SAT | REUSE — directly re-export existing reductions from the CR library |
| ReductionTest/DoubleSAT.lean | SAT -> DOUBLE-SAT | BUILD_NEW — build the encoding and reduction from scratch |
| ReductionTest/IndependentSet.lean | CLIQUE -> Independent Set | PARTIAL — reuse the CR complement-graph infrastructure |

## CR Advisor Reports

The advisor-reports/ directory contains the 3 analysis reports generated before proving by the ComplexityReduction advisor subagent, each determining the reuse strategy for its problem (REUSE / BUILD_NEW / PARTIAL) and locating the relevant CR library APIs. The final proof strategies match the report recommendations exactly.

## Build

```powershell
lake build ReductionTest
```

Depends on ComplexityReduction (local path ../ComplexityReduction) and mathlib (v4.29.0); the lean-toolchain is leanprover/lean4:v4.29.0.

## Blueprint

blueprint/src/ contains semi-formal LaTeX documents describing the mathematical proof idea of each reduction problem.

## Credits

- The ComplexityReduction library was developed by a senior member of our lab; this project consumes it as a local Lake dependency (`../ComplexityReduction`).
- Archon is used in its fork form: targeted modifications were made to the upstream frenzymath/Archon for the ComplexityReduction integration.
- Problem selection, blueprints, proof runs, and this repository were produced by the project author.

## Known Limitation

The theorems in `ReductionTest/` formalize the existence and correctness of each reduction (the
yes-instance iff), but **not** the polynomial-time computability of the reduction maps, so the
natural-language NP-completeness claims remain stronger than the formal statements. See Section 10
of `REDUCTION_TEST_REPORT` in the docs repository for the full discussion.
