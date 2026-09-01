# CR Advisor: independentset
**Iter:** 004

## Verdict
PARTIAL

The source problem (CLIQUE) is fully encoded in CR and axiom-clean. The target
(INDEPENDENT SET) does not exist anywhere in the library and must be built from
scratch. The complement-graph infrastructure and the `CostedReduction`
construction pattern are reusable from `Karp21/VertexCover.lean`; the CLIQUE to
IS reduction is strictly simpler than the CLIQUE to VC reduction already proven
there (no budget transform, no `noInstance` guard).

## Findings

### Source: CLIQUE — EXISTS in CR (axiom-clean)
- `cliqueDecisionProblem : EncodedDecisionProblem` in
  `ComplexityReduction/Combinatorics/Graph/Basic.lean:169`
  (namespace `ComplexityReduction.Combinatorics.Graph`), `isYes := Clique`.
- `CliqueInput` (`Basic.lean:125`): `{ graph : GraphInput, k : Nat }`.
- `Clique (I : CliqueInput) : Prop` (`Basic.lean:161`):
  `∃ vs, vs.length = I.k ∧ vs.Nodup ∧ VerticesWithinBounds I.graph vs ∧
     PairwiseAdjacent I.graph vs`.
- Graph infrastructure (`Basic.lean`, same namespace): `GraphInput`
  (`{ vertices, edges, directed }`, line 18), `HasUndirectedEdge`,
  `VerticesWithinBounds`, `PairwiseAdjacent`, `WellFormed`,
  `graphEncodedType`/`cliqueEncodedType` (raw `EncodedType.raw`).
- NPC theorem `Clique.cliqueNPComplete : NPCompleteEnc CostedPolyTimeModel
  cliqueDecisionProblem` in `Karp21/Clique/Part4.lean`
  (namespace `ComplexityReduction.Karp21.Clique`), no
  `sorry`/`admit`/`axiom`/`native_decide`.
- Fully qualified name the prover should reference:
  `ComplexityReduction.Combinatorics.Graph.cliqueDecisionProblem`.
  Openable via `open ComplexityReduction.Combinatorics.Graph`.

### Target: INDEPENDENT SET — DOES NOT EXIST in CR
- `Select-String` for `independentSet`/`IndependentSet`/`IndependentSetInput`
  across every `.lean` file under
  `D:\code\Lean\ComplexityReduction\ComplexityReduction\` returns **zero
  matches**.
- Not in `Karp21.Problem` enum (IS is not one of Karp's 21), so there is no
  `NPCTargetDescriptor` for it. Must be built from scratch.

### Bridge: complement-graph machinery — REUSABLE from VertexCover.lean
`Karp21/VertexCover.lean` (namespace `ComplexityReduction.Karp21.VertexCover`,
opens `ComplexityReduction.Combinatorics.Graph`) is a near-perfect template.
Verified axiom-clean (no `sorry`/`admit`/`axiom`/`native_decide`).

- `complementEdges (g : GraphInput) : List (Nat × Nat)` (line 38) — delegates to
  `structuredComplementEdges`.
- `complementGraph (g : GraphInput) : GraphInput` (noncomputable, line 50) —
  `{ vertices := g.vertices, edges := complementEdges g, directed := false }`.
- `hasUndirectedEdge_complementGraph_iff (g) (u v) :
    HasUndirectedEdge (complementGraph g) u v ↔
      u < g.vertices ∧ v < g.vertices ∧ u ≠ v ∧ ¬ HasUndirectedEdge g u v`
  (line 67) — **the key iff lemma**; this is the entire mathematical heart of
  the clique-to-independent-set correspondence.
- `mem_complementEdges_iff` (line 41), `complementGraph_wellFormed` (line 90),
  `complementEdges_length_le` (`≤ g.vertices * g.vertices`),
  `complementEdges_structured_inputSize_le`,
  `complementGraph_structured_inputSize_le` (line ~94) — size bounds for the
  `CostedMap`/`PolynomialSizeBound` witness.
- `hasUndirectedEdge_comm` (line 55) — symmetry helper used by the iff proof.
- The VC `map` (line 113) is `if I.k ≤ I.graph.vertices then
  { graph := complementGraph I.graph, k := I.graph.vertices - I.k } else
  noInstance` — i.e. VC applies a **budget transform `k ↦ n - k`** with a
  `noInstance` guard. The IS reduction needs **neither**: the map is just
  `{ graph := complementGraph I.graph, k := I.k }`.
- TM-backed polytime infrastructure lives in
  `Karp21/GraphStructuredTM/ComplementEdges.lean` (axiom-clean) and is
  assembled in VertexCover.lean via `cliqueToVertexCoverStructured_tm_polytime`
  (line 368) and `cliqueToVertexCoverStructured_polynomialSizeBound` (line 551).

### CostedReduction API (Certificates/ReductionCert.lean)
- `structure CostedReduction (A B : EncodedDecisionProblem)` (line 12):
  `f`, `correct : ∀ x, A.isYes x ↔ B.isYes (f x)`,
  `costed : CostedPolyTimeMap f`.
- `CostedReduction.ofCostedMap f hCorrect hCosted` (line 38), where
  `hCosted : CostedMap A.Instance B.Instance f` — the simplest constructor;
  `costed := CostedPolyTimeMap.of_costed hCosted`.
- `CostedReduction.toKarpReductionM` (line 32) and `.toSemantic` (line 26)
  available if an NPC wrapper (`NPCompleteEnc.transfer`) is wanted later.
- `CostedMap.of_encodedPolynomialSizeBound` (see `Certificates/CostedMap.lean`)
  builds the `CostedMap` from a `PolynomialSizeBound` witness
  (`Core/SizeBound.lean`, `PolynomialSizeBound.intro_with`).
- VertexCover.lean's heavier path (TM-backed) is also reusable:
  `TMBackedCostedMap` -> `TMBackedCostedReduction.ofTMBackedCostedMap ... map_correct`
  -> `.toCostedKarpReduction`. This yields a `KarpReductionM CostedPolyTimeModel`,
  which is what `NPCompleteEnc.transfer` consumes. `CostedReduction.ofCostedMap`
  is the lighter path and suffices for the blueprint's `CostedReduction` goal.

### Blueprint expectations (blueprint/src/chapters/ReductionTest_IndependentSet.tex)
Three `\lean{...}` declarations, all in namespace `ReductionTest.IndependentSet`:
1. `independentSetDecisionProblem : EncodedDecisionProblem`
2. `cliqueToIndependentSet : CostedReduction <source> <target>`
3. `cliqueToIndependentSet_correct` (correctness iff:
   `cliqueDecisionProblem.isYes I ↔ independentSetDecisionProblem.isYes (map I)`)

### Current stub (ReductionTest/IndependentSet.lean)
Imports only `Mathlib`, `ComplexityReduction.SAT.ThreeSAT`,
`ComplexityReduction.Certificates.ReductionCert`; namespace
`ReductionTest.IndependentSet`; only a `placeholder_independentSet : True`
theorem. The SAT import is unused for this reduction; the relevant imports are
the graph + VertexCover modules (see Recommendation).

## Recommendation
Define INDEPENDENT SET from scratch mirroring the CLIQUE pattern in
`Combinatorics/Graph/Basic.lean`, then build the `CostedReduction` by adapting
the complement-graph construction from `Karp21/VertexCover.lean` (strictly
simpler: no budget transform, no `noInstance` guard).

Concrete scaffold for the prover (all in `ReductionTest/IndependentSet.lean`,
namespace `ReductionTest.IndependentSet`):

- Define `IndependentSetInput` mirroring `CliqueInput`:
  `structure IndependentSetInput where graph : GraphInput; k : Nat`.
- Define the predicate mirroring `Clique` but with the opposite adjacency
  condition. `PairwiseAdjacent` says every distinct pair is adjacent; the
  independent-set condition is every distinct pair is **not** adjacent:
  `def IndependentSet (I : IndependentSetInput) : Prop :=
     ∃ vs : List Nat, vs.length = I.k ∧ vs.Nodup ∧
       VerticesWithinBounds I.graph vs ∧
       ∀ u ∈ vs, ∀ v ∈ vs, u ≠ v → ¬ HasUndirectedEdge I.graph u v`.
- Define `independentSetEncodedType : EncodedType := EncodedType.raw
  IndependentSetInput` and
  `independentSetDecisionProblem : EncodedDecisionProblem where
    Instance := independentSetEncodedType; isYes := IndependentSet`
  (parallel to `cliqueDecisionProblem`).
- Define the reduction map (no guard needed):
  `noncomputable def cliqueToIndependentSetMap (I : CliqueInput) :
     IndependentSetInput := { graph := complementGraph I.graph, k := I.k }`.
- Prove the correctness iff using
  `hasUndirectedEdge_complementGraph_iff`: a set `U` is pairwise adjacent in
  `G` iff it is pairwise non-adjacent in `complementGraph G`, with the same
  vertex bounds (`complementGraph` preserves `vertices`). This is exactly the
  lemma `cliqueToIndependentSet_correct` should state:
  `∀ I, cliqueDecisionProblem.isYes I ↔
     independentSetDecisionProblem.isYes (cliqueToIndependentSetMap I)`.
- Build `cliqueToIndependentSet : CostedReduction cliqueDecisionProblem
  independentSetDecisionProblem` via `CostedReduction.ofCostedMap`, supplying
  a `CostedMap`/`PolynomialSizeBound` witness. The size bound follows from
  `complementGraph_structured_inputSize_le` (complement graph output is
  `O(vertices^2)`, bounded by a cubic in the input size), and the polytime
  map follows from the existing complement-edge TM machinery in
  `Karp21/GraphStructuredTM/ComplementEdges.lean`. If the prover prefers the
  lighter path, `CostedMap.of_encodedPolynomialSizeBound` with a
  `PolynomialSizeBound.intro_with` witness (degree 3, as in VertexCover's
  `cliqueToVertexCoverStructured_polynomialSizeBound`) suffices; if a full
  TM-backed certificate is wanted, mirror VertexCover's
  `TMBackedCostedMap`/`TMBackedCostedReduction.ofTMBackedCostedMap` flow.

Imports the prover should add (the current stub is missing all of these):

- `ComplexityReduction.Combinatorics.Graph` — `GraphInput`, `HasUndirectedEdge`,
  `VerticesWithinBounds`, `PairwiseAdjacent`, `CliqueInput`, `Clique`,
  `cliqueDecisionProblem`, `cliqueEncodedType`, `WellFormed`.
- `ComplexityReduction.Karp21.VertexCover` — `complementGraph`,
  `complementEdges`, `hasUndirectedEdge_complementGraph_iff`,
  `mem_complementEdges_iff`, `complementGraph_wellFormed`,
  `complementGraph_structured_inputSize_le`, `complementEdges_length_le`,
  `complementEdges_structured_inputSize_le`, `hasUndirectedEdge_comm`.
- `ComplexityReduction.Certificates.ReductionCert` (already imported) —
  `CostedReduction`, `CostedReduction.ofCostedMap`.
- `ComplexityReduction.Certificates.CostedMap` — `CostedMap`,
  `CostedMap.of_encodedPolynomialSizeBound`, `CostedPolyTimeMap.of_costed`.
- `ComplexityReduction.Core.SizeBound` — `PolynomialSizeBound`,
  `PolynomialSizeBound.intro_with` (only if using the size-bound constructor).
- `ComplexityReduction.Karp21.GraphStructuredTM` (and its
  `ComplementEdges.lean` sub-module) — only if the prover opts for the
  TM-backed polytime path instead of the lighter `CostedMap` route.

Every declaration recommended above is axiom-clean.

## Critical references
- `D:\code\Lean\ComplexityReduction\ComplexityReduction\Combinatorics\Graph\Basic.lean`
  — graph types, CLIQUE encoding (`cliqueDecisionProblem` at line 169),
  `VertexCoverInput`/`VertexCover`/`vertexCoverDecisionProblem` (lines 179-228)
  as the structural template for the new IS declarations.
- `D:\code\Lean\ComplexityReduction\ComplexityReduction\Karp21\VertexCover.lean`
  — complement-graph `CostedReduction` template (`complementGraph` line 50,
  `hasUndirectedEdge_complementGraph_iff` line 67, `map` line 113,
  `CostedReduction`/`KarpReductionM` construction lines 551-604).
- `D:\code\Lean\ComplexityReduction\ComplexityReduction\Certificates\ReductionCert.lean`
  — `CostedReduction` structure (line 12), `ofCostedMap` (line 38).
- `D:\code\Lean\ComplexityReduction\ComplexityReduction\Certificates\CostedMap.lean`
  — `CostedMap`, `CostedMap.of_encodedPolynomialSizeBound`,
  `CostedPolyTimeMap.of_costed`.
- `D:\code\Lean\ComplexityReduction\ComplexityReduction\Core\SizeBound.lean`
  — `PolynomialSizeBound`, `PolynomialSizeBound.intro_with`.
- `D:\code\Lean\ComplexityReduction\ComplexityReduction\Karp21\GraphStructuredTM\ComplementEdges.lean`
  — TM-backed complement-edge polytime map (optional heavier path).
- `D:\code\Lean\reduction-test\blueprint\src\chapters\ReductionTest_IndependentSet.tex`
  — expected `\lean{...}` declarations.
- `D:\code\Lean\reduction-test\ReductionTest\IndependentSet.lean` — current stub.
