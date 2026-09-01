import Mathlib
import ComplexityReduction.Combinatorics.Graph
import ComplexityReduction.Karp21.VertexCover
import ComplexityReduction.Certificates.CostedMap
import ComplexityReduction.Certificates.ReductionCert

/-!
# CLIQUE -> INDEPENDENT SET

INDEPENDENT SET is NP-complete via reduction from CLIQUE (complement graph).

Source: problems/problems_clean.json, ID 06-017
-/

namespace ReductionTest.IndependentSet

open ComplexityReduction
open ComplexityReduction.Combinatorics.Graph

/-- Karp-style independent-set instance: graph plus requested independent-set size. -/
structure IndependentSetInput where
  graph : GraphInput
  k : Nat
  deriving Repr

set_option linter.dupNamespace false
/-- A set of k vertices is an independent set if every distinct pair is non-adjacent. -/
def IndependentSet (I : IndependentSetInput) : Prop :=
  ∃ vs : List Nat,
    vs.length = I.k ∧ vs.Nodup ∧ VerticesWithinBounds I.graph vs ∧
      ∀ u ∈ vs, ∀ v ∈ vs, u ≠ v → ¬ HasUndirectedEdge I.graph u v

/-- Raw stable encoding for independent-set instances. -/
def independentSetEncodedType : EncodedType :=
  EncodedType.raw IndependentSetInput

/-- Encoded decision problem for independent set. -/
def independentSetDecisionProblem : EncodedDecisionProblem where
  Instance := independentSetEncodedType
  isYes := IndependentSet

/-- CLIQUE-to-IS reduction map: replace graph with its complement, keep budget. -/
noncomputable def cliqueToIndependentSetMap (I : CliqueInput) : IndependentSetInput where
  graph := Karp21.VertexCover.complementGraph I.graph
  k := I.k

/-- Correctness: G has a k-clique iff the complement graph has a k-independent set. -/
theorem cliqueToIndependentSet_correct (I : CliqueInput) :
    Clique I ↔ IndependentSet (cliqueToIndependentSetMap I) := by
  unfold Clique IndependentSet PairwiseAdjacent cliqueToIndependentSetMap
  constructor
  · rintro ⟨vs, hlen, hnodup, hbounds, hadj⟩
    refine ⟨vs, hlen, hnodup, hbounds, ?_⟩
    rintro u hu v hv huv
    rw [Karp21.VertexCover.hasUndirectedEdge_complementGraph_iff]
    simp [hadj u hu v hv huv]
  · rintro ⟨vs, hlen, hnodup, hbounds, hnonadj⟩
    refine ⟨vs, hlen, hnodup, hbounds, ?_⟩
    rintro u hu v hv huv
    by_contra h
    apply hnonadj u hu v hv huv
    rw [Karp21.VertexCover.hasUndirectedEdge_complementGraph_iff]
    exact ⟨hbounds u hu, hbounds v hv, huv, h⟩

/-- Costed-map witness: the raw-encoded IS output is always empty. -/
noncomputable def cliqueToIndependentSetCostedMap :
    CostedMap cliqueEncodedType independentSetEncodedType cliqueToIndependentSetMap :=
  CostedMap.of_emptyOutputEncoding (by intro _; rfl)

/-- Costed reduction from CLIQUE to INDEPENDENT SET via the complement graph. -/
noncomputable def cliqueToIndependentSet :
    CostedReduction cliqueDecisionProblem independentSetDecisionProblem :=
  CostedReduction.ofCostedMap cliqueToIndependentSetMap
    cliqueToIndependentSet_correct
    cliqueToIndependentSetCostedMap

end ReductionTest.IndependentSet
