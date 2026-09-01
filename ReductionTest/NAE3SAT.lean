import Mathlib
import ComplexityReduction.SAT.ThreeSAT
import ComplexityReduction.Certificates.ReductionCert
import ComplexityReduction.CSP.Examples.NAE3SAT
import ComplexityReduction.CSP.Hardness.NAE3SAT

/-!
# 3SAT -> NAE-3SAT

NAE-3SAT (Not-All-Equal 3SAT) is NP-complete via reduction from 3SAT.

Source: problems/problems_clean.json, ID 02-004
-/

namespace ReductionTest.NAE3SAT

open ComplexityReduction

/- NAE-3SAT decision problem, re-exported from the ComplexityReduction library. -/
noncomputable abbrev nae3SATDecisionProblem : EncodedDecisionProblem :=
  CSP.Examples.notAllEqual3DecisionProblem

/- Costed reduction from 3SAT to NAE-3SAT, re-exported from the ComplexityReduction library. -/
noncomputable abbrev threeSATToNAE3SAT :
    CostedReduction SAT.threeSATDecisionProblem nae3SATDecisionProblem :=
  CSP.Hardness.NAE3SAT.threeSATToNAE3CostedReduction

/- Correctness: a 3SAT formula is a yes-instance iff its NAE-3SAT image is a yes-instance. -/
theorem threeSATToNAE3SAT_correct (φ : SAT.ThreeCNF) :
    SAT.threeSATDecisionProblem.isYes φ ↔
    nae3SATDecisionProblem.isYes (CSP.Hardness.NAE3SAT.threeCNFToNAE3Formula φ) := by
  -- Reuse the CR library iff; both `isYes` predicates are defeq to the
  -- corresponding `Satisfiable` (via `threeSATDecisionProblem_isYes_iff` and
  -- `boolCSPDecisionProblem_isYes_iff`, both `Iff.rfl`), and
  -- `nae3SATDecisionProblem` is an `abbrev` for `notAllEqual3DecisionProblem`.
  exact (CSP.Hardness.NAE3SAT.threeCNFToNAE3Formula_satisfiable_iff φ).symm

end ReductionTest.NAE3SAT
