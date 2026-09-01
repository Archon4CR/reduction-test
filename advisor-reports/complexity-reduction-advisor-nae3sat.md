# CR Advisor: nae3sat
**Iter:** 001

## Verdict
REUSE

The ComplexityReduction library already encodes both problems and ships a
fully-proven, axiom-clean 3SAT -> NAE-3SAT hardness reduction. The prover
should re-export/wrap existing declarations in `ReductionTest/NAE3SAT.lean`,
not build from scratch.

## Findings

### Source: 3SAT (already in CR)
- **Declaration**: `ComplexityReduction.SAT.threeSATDecisionProblem : EncodedDecisionProblem`
  (in `SAT/ThreeSAT.lean`).
- **Target alias**: `Targets.threeSATDecisionProblem` is `abbrev` for
  `SAT.threeSATDecisionProblem` (in `Targets/ThreeSAT.lean`), so the two are
  definitionally equal.
- **EncodedDecisionProblem**: `threeSATSatLike.toDecisionProblem`, where
  `threeSATSatLike : SatLikeProblem` has `Inst := threeCNFEncodedType`,
  `Assignment := fun _ => Assignment`, `Satisfies := fun φ a => φ.Satisfies a`.
- **Carrier type**: `ThreeCNF` (from `threeCNFEncodedType : EncodedType` with
  `Carrier := ThreeCNF`, `Symbol := ThreeSATSymbol = Option (Bool ⊕ Bool)`).
- **isYes iff**: `threeSATDecisionProblem.isYes φ ↔ φ.Satisfiable`
  (simp lemma `threeSATDecisionProblem_isYes_iff`).

### Target: NAE-3SAT (already in CR)
- **Declaration**: `ComplexityReduction.CSP.Examples.notAllEqual3DecisionProblem :
  EncodedDecisionProblem` (in `CSP/Examples/NAE3SAT.lean`).
- **Definition**: `boolCSPDecisionProblem notAllEqual3Language` (i.e.
  `(boolCSPSatLike notAllEqual3Language).toDecisionProblem`).
- **Carrier type**: `Formula notAllEqual3Language`
  (`formulaEncodedType Γ` has `Carrier := Formula Γ`; `Symbol := FormulaSymbol Γ`).
- **Language**: `notAllEqual3Language : BoolLanguage` with
  `Symbol := NAE3Symbol` (inductive, singleton `rel`), `relationOf := fun _ => notAllEqual3Rel`,
  where `notAllEqual3Rel := StandardRelations.notAllEqual3Rel` (arity 3,
  not-all-equal). `notAllEqual3Language_isThreeBounded` holds.
- **isYes predicate**: `(boolCSPDecisionProblem Γ).isYes φ ↔ Formula.Satisfiable φ`
  (simp lemma `boolCSPDecisionProblem_isYes_iff`, `CSP/SatLike.lean`). For NAE-3SAT:
  `notAllEqual3DecisionProblem.isYes φ ↔ Formula.Satisfiable φ`
  (`φ : Formula notAllEqual3Language`).

### Bridge: 3SAT -> NAE-3SAT hardness reduction (already proven)
All in `CSP/Hardness/NAE3SAT/Part2.lean` (aggregated by `CSP/Hardness/NAE3SAT.lean`).
Axiom-clean: no `sorry`/`admit`/`axiom`/`native_decide` in any NAE3SAT file.

- **Map**: `threeCNFToNAE3Formula (φ : ThreeCNF) : Formula Examples.notAllEqual3Language`
  (Part1). Gadget: global false/true anchors (`falseVar`, `trueVar`) + an anchor
  NAE constraint; per-source-variable complement-pair constraints via `negVar`;
  per-clause gadgets using auxiliary vars `auxVar`/`auxNegVar`. This is the
  standard "add reference constants + auxiliary vars" approach the directive
  describes (uses a false/true anchor pair rather than a single `z`).
- **Correctness iff**: `threeCNFToNAE3Formula_satisfiable_iff (φ : ThreeCNF) :
  Formula.Satisfiable (threeCNFToNAE3Formula φ) ↔ φ.Satisfiable` (Part2, fully proved).
- **SemanticReduction**: `threeSATToNAE3Reduction :
  SemanticReduction SAT.threeSATDecisionProblem Examples.notAllEqual3DecisionProblem`
  (`.correct := threeCNFToNAE3Formula_satisfiable_iff.symm`).
- **CostedReduction**: `threeSATToNAE3CostedReduction :
  CostedReduction SAT.threeSATDecisionProblem Examples.notAllEqual3DecisionProblem`
  (via `CostedReduction.ofCostedMap` + `PolynomialSizeBound`, degree 2, coeffs
  800/200; bound `threeCNFToNAE3Formula_encodedLength_le_quadratic`).
- **KarpReductionM**: `threeSATToNAE3KarpReduction :
  KarpReductionM CostedPolyTimeModel SAT.threeSATDecisionProblem
  Examples.notAllEqual3DecisionProblem` (via `.toKarpReductionM`).
- **NPC theorem**: `CSP.Hardness.NAE3SAT.nae3NPComplete :
  NPCompleteEnc CostedPolyTimeModel Examples.notAllEqual3DecisionProblem`
  (in `CSP/Hardness/NAE3SATNPC.lean`), using the discharged P14e 3SAT
  completeness boundary + `threeSATToNAE3KarpReduction`. Conditional variants:
  `nae3NPComplete_of_threeSAT`, `nae3NPComplete_of_threeSAT_only`,
  `nae3NPComplete_fromBoundary`; membership `nae3InNP_of_threeSATInNP`.
- **Upper-bound direction** (NAE-3SAT -> 3SAT, also already present in
  `CSP/Examples/NAE3SAT.lean`): `notAllEqual3ToThreeSATCostedReduction`,
  `notAllEqual3ToThreeSATKarpReduction`, `notAllEqual3ToThreeSATReduction` —
  the generic `boolCSPToThreeSAT` bridge specialized to NAE-3SAT.

### CostedReduction vs LogReductionCert
- The existing reduction is a **`CostedReduction`** (poly-time) and derivable as a
  **`KarpReductionM CostedPolyTimeModel`**. There is **no `LogReductionCert` /
  log-space variant** for NAE-3SAT (grep for `LogReductionCert`/`LogSpace`/
  `StrictLogSpace` in the NAE3SAT files returns nothing). So: use `CostedReduction`,
  not `LogReductionCert`.

### Related but separate (do NOT confuse with the ordinary target)
- `CSP/Hardness/NAE3SATPinned.lean` defines a *pinned, polarized* variant:
  `nae3PinnedDecisionProblem` over `nae3PinnedLanguage` (8 polarity-tagged NAE
  symbols + a `pinFalse` symbol), with `threeSATToNAE3PinnedCostedReduction`.
  This is a different language; the directive's target is the ordinary
  singleton-language `notAllEqual3DecisionProblem`, not the pinned one.

## Recommendation
Reuse verbatim. Map the planned scaffold onto existing declarations:

| Planned scaffold                        | Reuse                                                        |
|-----------------------------------------|--------------------------------------------------------------|
| `nae3SATDecisionProblem : EncodedDecisionProblem` | `CSP.Examples.notAllEqual3DecisionProblem`          |
| `threeSATToNAE3SAT : CostedReduction threeSATDecisionProblem nae3SATDecisionProblem` | `CSP.Hardness.NAE3SAT.threeSATToNAE3CostedReduction` |
| `threeSATToNAE3SAT_correct` (correctness iff) | `CSP.Hardness.NAE3SAT.threeCNFToNAE3Formula_satisfiable_iff` (or `.correct`) |

Action for the prover: in `ReductionTest/NAE3SAT.lean`, add imports
`ComplexityReduction.CSP.Examples.NAE3SAT` and
`ComplexityReduction.CSP.Hardness.NAE3SAT` (the current stub imports only
`SAT.ThreeSAT` + `Certificates.ReductionCert`), then define abbrev/re-exports
under `ReductionTest.NAE3SAT` pointing at the declarations above. No new proof
obligations are required; if an NPC wrapper is wanted, `nae3NPComplete` is
already available.
