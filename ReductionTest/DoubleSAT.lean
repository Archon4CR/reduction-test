import Mathlib
import ComplexityReduction.SAT.ThreeSAT
import ComplexityReduction.Certificates.ReductionCert
import ComplexityReduction.Karp21.Satisfiability.Encoding
import ComplexityReduction.Karp21.Satisfiability.SplitWith.Core
import ComplexityReduction.Karp21.Satisfiability.SplitWith.SizeAndFinalMaps
import ComplexityReduction.Bridges.CostedToTM.NatRange

/-!
# SAT -> DOUBLE-SAT

DOUBLE-SAT (boolean formula with at least two satisfying assignments) is
NP-complete via reduction from SAT.

Source: problems/problems_clean.json, ID 01-001
-/

namespace ReductionTest.DoubleSAT

open ComplexityReduction

/-- DOUBLE-SAT decision problem: a CNF formula with at least two distinct
satisfying assignments. -/
def doubleSATDecisionProblem : EncodedDecisionProblem where
  Instance := Karp21.cnfStructuredEncodedType
  isYes := fun phi =>
    ∃ a1 a2 : SAT.Assignment,
      a1 ≠ a2 ∧ SAT.CNF.Satisfies phi a1 ∧ SAT.CNF.Satisfies phi a2

/-- The SAT-to-DOUBLE-SAT reduction map appends a tautological clause
`[Literal.positive y, Literal.negative y]` where `y = CNF.varBound phi`
is a fresh variable not occurring in `phi`. -/
def satToDoubleSATMap (phi : SAT.CNF) : SAT.CNF :=
  phi ++ [[SAT.Literal.positive (SAT.CNF.varBound phi),
           SAT.Literal.negative (SAT.CNF.varBound phi)]]

/-- Correctness of the SAT-to-DOUBLE-SAT reduction: `phi` is satisfiable iff
`satToDoubleSATMap phi` has at least two distinct satisfying assignments. -/
theorem satToDoubleSAT_correct (phi : SAT.CNF) :
    SAT.CNF.Satisfiable phi ↔
      doubleSATDecisionProblem.isYes (satToDoubleSATMap phi) := by
  constructor
  · -- Forward: phi satisfiable => f(phi) has >= 2 satisfying assignments
    rintro ⟨σ, hσ⟩
    set y := SAT.CNF.varBound phi
    -- Changing σ at the fresh variable y does not affect satisfaction of phi,
    -- since every variable of phi is < y (clause_vars_lt_varBound).
    have hphi : ∀ b, SAT.CNF.Satisfies phi (SAT.Clause.setVar σ y b) := by
      intro b c hc
      rcases hσ c hc with ⟨l, hl, hlEval⟩
      refine ⟨l, hl, ?_⟩
      have hlv : l.var < y := SAT.CNF.clause_vars_lt_varBound hc l hl
      rw [SAT.Clause.literal_eval_eq_of_var_eq l
          (SAT.Clause.setVar_ne (ne_of_lt hlv))]
      exact hlEval
    -- The tautological clause [pos y, neg y] is satisfied by any assignment
    have htaut_cnf : ∀ a, SAT.CNF.Satisfies
        [[SAT.Literal.positive y, SAT.Literal.negative y]] a := by
      intro a c hc
      rcases List.mem_cons.mp hc with rfl | h
      · cases hay : a y
        · exact ⟨SAT.Literal.negative y, by simp, by simp [hay]⟩
        · exact ⟨SAT.Literal.positive y, by simp, by simp [hay]⟩
      · cases h
    -- Both setVar variants satisfy the appended formula, via satisfies_append
    have hall : ∀ b, SAT.CNF.Satisfies (satToDoubleSATMap phi)
        (SAT.Clause.setVar σ y b) := by
      intro b
      rw [satToDoubleSATMap, SAT.CNF.satisfies_append]
      exact ⟨hphi b, htaut_cnf _⟩
    -- The two assignments are distinct (they differ at y)
    have hne : SAT.Clause.setVar σ y true ≠ SAT.Clause.setVar σ y false := by
      intro h
      have heq := congr_fun h y
      simp [SAT.Clause.setVar_self] at heq
    exact ⟨SAT.Clause.setVar σ y true, SAT.Clause.setVar σ y false, hne, hall true, hall false⟩
  · -- Backward: f(phi) has >= 2 satisfying assignments => phi satisfiable
    rintro ⟨a₁, a₂, _hne, h₁, _h₂⟩
    rw [satToDoubleSATMap, SAT.CNF.satisfies_append] at h₁
    exact ⟨a₁, h₁.1⟩

/-- SAT reduces to DOUBLE-SAT via a polynomial-time costed reduction. -/
noncomputable def satToDoubleSAT :
    CostedReduction Karp21.satisfiabilityStructuredDecisionProblem
      doubleSATDecisionProblem :=
  CostedReduction.ofCostedMap satToDoubleSATMap satToDoubleSAT_correct
    (CostedMap.of_encodedPolynomialSizeBound
      (PolynomialSizeBound.of_linear
        (LinearSizeBound.intro_with 3 9 (by
          intro phi
          change Karp21.cnfStructuredEncodedType.inputSize (satToDoubleSATMap phi) ≤
              3 * Karp21.cnfStructuredEncodedType.inputSize phi + 9
          have hy_le : SAT.CNF.varBound phi ≤ Karp21.cnfStructuredEncodedType.inputSize phi :=
            Karp21.cnfVarBound_le_cnfStructured_inputSize phi
          have hSingleton : Karp21.cnfStructuredEncodedType.inputSize
              [[SAT.Literal.positive (SAT.CNF.varBound phi),
                SAT.Literal.negative (SAT.CNF.varBound phi)]] =
              2 * SAT.CNF.varBound phi + 9 := by
            have hp : (SAT.Literal.positive (SAT.CNF.varBound phi)).var =
                SAT.CNF.varBound phi := rfl
            have hn : (SAT.Literal.negative (SAT.CNF.varBound phi)).var =
                SAT.CNF.varBound phi := rfl
            simp only [Karp21.cnfStructuredEncodedType, Karp21.clauseStructuredEncodedType,
              EncodedType.inputSize_list_cons, EncodedType.inputSize_list_nil,
              Karp21.literalStructured_inputSize_eq, hp, hn]
            omega
          have hAppend : Karp21.cnfStructuredEncodedType.inputSize (satToDoubleSATMap phi) =
              Karp21.cnfStructuredEncodedType.inputSize phi +
                Karp21.cnfStructuredEncodedType.inputSize
                  [[SAT.Literal.positive (SAT.CNF.varBound phi),
                  SAT.Literal.negative (SAT.CNF.varBound phi)]] := by
            exact list_inputSize_append Karp21.clauseStructuredEncodedType phi
              [[SAT.Literal.positive (SAT.CNF.varBound phi),
                SAT.Literal.negative (SAT.CNF.varBound phi)]]
          rw [hAppend, hSingleton]
          omega))))

end ReductionTest.DoubleSAT
