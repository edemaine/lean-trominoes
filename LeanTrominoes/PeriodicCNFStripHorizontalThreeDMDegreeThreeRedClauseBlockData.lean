/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMDegreeThreeRedClauseData
import LeanTrominoes.PeriodicCNFStripDirectSparseAffineVertexRequestTripleIndexed

/-! # Indexed red clause-element blocks -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  horizontalThreeDMTripleVariableDecidableEq

def horizontalThreeDMRedClauseElementsZippedComputed
    (source : PeriodicCNF Nat) : List (RedElement RoutedVariable) :=
  let typed := horizontalThreeDMTypedSourceComputed source
  typed.clauses.zipIdx.flatMap fun tagged =>
    [.clauseInternal tagged.2] ++
      allTerminalGroups.map (RedElement.clauseTerminal tagged.2)

/-- The range-indexed clause suffix is exactly the same stable scan paired
with its clause data. -/
theorem horizontalThreeDMRedClauseElementsComputed_eq_zipped
    (source : PeriodicCNF Nat) :
    horizontalThreeDMRedClauseElementsComputed source =
      horizontalThreeDMRedClauseElementsZippedComputed source := by
  unfold horizontalThreeDMRedClauseElementsComputed
    horizontalThreeDMRedClauseElementsZippedComputed
  exact range_getD_flatMap_eq_zipIdx
    (horizontalThreeDMTypedSourceComputed source).clauses []
    (fun (_clause : PeriodicClause RoutedVariable) clauseIndex =>
      [RedElement.clauseInternal clauseIndex] ++
        allTerminalGroups.map
          (RedElement.clauseTerminal clauseIndex))

/-- The explicit degree-three red block contributed by each binary or
ternary clause. -/
def horizontalThreeDMRedDegreeThreeClauseElementsComputed
    (source : PeriodicCNF Nat) : List (RedElement RoutedVariable) :=
  let typed := horizontalThreeDMTypedSourceComputed source
  typed.clauses.zipIdx.flatMap fun tagged =>
    [.clauseInternal tagged.2,
      .clauseTerminal tagged.2 .top,
      .clauseTerminal tagged.2 .left] ++
      if tagged.1.length = 3 then
        [.clauseTerminal tagged.2 .right]
      else []

end PeriodicCNFStripReduction
end LeanTrominoes
