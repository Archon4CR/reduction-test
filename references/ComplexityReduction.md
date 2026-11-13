# ComplexityReduction Project Reference

This document records how `archon-test` integrates the ComplexityReduction library. It stays consistent with
`complexity-reduction-library.md` in the Archon packaging data and adds the concrete goals and import strategy currently needed by this project.

## Local Dependency

- Lake declaration: `require ComplexityReduction from "../ComplexityReduction"` (see `lakefile.lean`).
- Source path: `../ComplexityReduction`; the inner library directory is `../ComplexityReduction/ComplexityReduction`.
- Toolchain: `leanprover/lean4:v4.29.0`, mathlib `v4.29.0`.

## Import Strategy

Use the aggregate target module as the default entry:

```lean
import ComplexityReduction.Targets
```

Supplement as needed when a wider symbol surface is required:

```lean
import ComplexityReduction.Core
import ComplexityReduction.SAT
import ComplexityReduction.CSP
import ComplexityReduction.Schaefer
import ComplexityReduction.Karp21
import ComplexityReduction.Bridges
import ComplexityReduction.Certificates
import ComplexityReduction.Templates
```

`Templates` is not included in the root import; it must be imported separately when reduction templates are used.

## Smoke Verification (Completed)

`ArchonTest/ComplexityReductionSmoke.lean` has passed `#check`:

- `ComplexityReduction.Targets.NPCTargetDescriptor : Type`
- `ComplexityReduction.Targets.threeSATDecisionProblem : ComplexityReduction.EncodedDecisionProblem`
- `ComplexityReduction.Targets.threeSATTarget : ComplexityReduction.Targets.NPCTargetDescriptor`
- `ComplexityReduction.Targets.localTargets : List ComplexityReduction.Targets.NPCTargetDescriptor`

Build command:

```powershell
& 'C:\Users\14354\.elan\toolchains\leanprover--lean4---v4.29.0\bin\lake.exe' build ArchonTest.ComplexityReductionSmoke
```

## Current Goals

This project does not yet define any ComplexityReduction-related proof goals. If a problem needs to be proved NP-complete later, you should:

1. Pick a target descriptor from `Targets.localTargets`.
2. Prefer reusing `CostedReduction.comp`, `Templates.*`, `NPCompleteEnc.transfer`, and `composeTMKarp`.
3. Every new declaration must compile and be axiom-clean; `#print axioms` is only allowed to show `propext`, `Classical.choice`, `Quot.sound`.

## Trust Boundary

Targets submodules available by default: `ThreeSAT`, `ThreeSATCompleteBoundary`, `NPCTargetCatalog`,
`Karp21Catalog`, `CountingCSP`, `FiniteDomainCSP`, `HColoringCatalog`,
`HColoringComplexityCatalog`, `NPCTransfer`.

The external Schaefer bridge modules that require explicit opt-in: `Targets.Schaefer`,
`Targets.SchaeferFiniteDomain`. These only record boundary metadata and do not carry external theorems into this project's
`EncodedDecisionProblem` foundation. Note the import-level difference: `Targets.Schaefer` is
imported indirectly by `NPCTargetCatalog` (only string constants are taken), so its types are in scope but it contains no external theorems;
`Targets.SchaeferFiniteDomain` is not imported by any default module. The substantive trust boundary is at the data level:
`localTargets`/`initialTargets` exclude external descriptors, and only `targetsWithExternalBridges` includes them.

## Searching the Library

Archon packages `search_complexity_reduction.sh`, which points to `../ComplexityReduction/ComplexityReduction` by default.
You can also use `rg` directly:

```bash
rg -n "NPCompleteEnc" ../ComplexityReduction/ComplexityReduction/
rg -l "Schaefer" ../ComplexityReduction/ComplexityReduction/
```

## Detailed Symbol Table

For the complete symbol table, see the Archon packaged reference `complexity-reduction-library.md`; it is not repeated here. This file only records the project-level integration status and local verification results.
