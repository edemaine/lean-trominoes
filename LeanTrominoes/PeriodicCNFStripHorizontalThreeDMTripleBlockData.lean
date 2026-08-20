/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalAssembledEdgeRouteData
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMTypedElementDegrees
import LeanTrominoes.PeriodicCNFStripDirectSparseAffineVertexRequestTripleIndexed

/-! # Explicit variable and clause blocks in the horizontal triple scan -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

/-- Variable-module prefix of the computed typed triple list. -/
def horizontalThreeDMVariableTriplesComputed
    (source : PeriodicCNF Nat) : List (Triple RoutedVariable) :=
  variableTriples (horizontalNormalizedRoutedFormulaComputed source).erase

/-- Nine clause-core triples per computed clause, with the clause data paired
with its stable clause index. -/
def horizontalThreeDMClauseTriplesZippedComputed
    (source : PeriodicCNF Nat) : List (Triple RoutedVariable) :=
  (horizontalNormalizedRoutedFormulaComputed source).erase.clauses.zipIdx.flatMap
    fun tagged =>
    allClauseSets.map (Triple.clause tagged.2)

/-- The range-indexed clause triple suffix is exactly the clause-data scan
paired with stable clause indices. -/
theorem clauseTriples_eq_zipIdx
    (typed : PeriodicCNF RoutedVariable) :
    clauseTriples typed =
      typed.clauses.zipIdx.flatMap fun tagged =>
        allClauseSets.map (Triple.clause tagged.2) := by
  unfold clauseTriples
  exact range_getD_flatMap_eq_zipIdx
    typed.clauses []
    (fun (_clause : PeriodicClause RoutedVariable) clauseIndex =>
      allClauseSets.map (Triple.clause clauseIndex))

theorem horizontalThreeDMClauseTriplesComputed_eq_zipped
    (source : PeriodicCNF Nat) :
    clauseTriples
        (horizontalNormalizedRoutedFormulaComputed source).erase =
      horizontalThreeDMClauseTriplesZippedComputed source := by
  unfold horizontalThreeDMClauseTriplesZippedComputed
  exact clauseTriples_eq_zipIdx
    (horizontalNormalizedRoutedFormulaComputed source).erase

/-- The complete computed typed triple list is the variable-module prefix
followed by the fixed nine-triple block of every clause. -/
theorem horizontalThreeDMTypedTriplesComputed_eq_blocks
    (source : PeriodicCNF Nat) :
    horizontalThreeDMTypedTriplesComputed source =
      horizontalThreeDMVariableTriplesComputed source ++
        horizontalThreeDMClauseTriplesZippedComputed source := by
  unfold horizontalThreeDMTypedTriplesComputed
    horizontalThreeDMVariableTriplesComputed
    horizontalThreeDMClauseTriplesZippedComputed
    triples
  exact congrArg
    (fun suffix =>
      variableTriples
          (horizontalNormalizedRoutedFormulaComputed source).erase ++
        suffix)
    (clauseTriples_eq_zipIdx
      (horizontalNormalizedRoutedFormulaComputed source).erase)

end PeriodicCNFStripReduction
end LeanTrominoes
