/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMDegreeThreeGreenClauseData
import LeanTrominoes.PeriodicCNFStripDirectSparseAffineVertexRequestTripleIndexed

/-! # Indexed green clause-element blocks -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  horizontalThreeDMTripleVariableDecidableEq

def horizontalThreeDMGreenClauseElementsZippedComputed
    (source : PeriodicCNF Nat) : List (GreenElement RoutedVariable) :=
  let typed := horizontalThreeDMTypedSourceComputed source
  typed.clauses.zipIdx.flatMap fun tagged =>
    [.clauseInternal tagged.2] ++
      allTerminalGroups.map (GreenElement.clauseTerminal tagged.2)

theorem horizontalThreeDMGreenClauseElementsComputed_eq_zipped
    (source : PeriodicCNF Nat) :
    horizontalThreeDMGreenClauseElementsComputed source =
      horizontalThreeDMGreenClauseElementsZippedComputed source := by
  unfold horizontalThreeDMGreenClauseElementsComputed
    horizontalThreeDMGreenClauseElementsZippedComputed
  exact range_getD_flatMap_eq_zipIdx
    (horizontalThreeDMTypedSourceComputed source).clauses []
    (fun (_clause : PeriodicClause RoutedVariable) clauseIndex =>
      [GreenElement.clauseInternal clauseIndex] ++
        allTerminalGroups.map
          (GreenElement.clauseTerminal clauseIndex))

def horizontalThreeDMGreenDegreeThreeClauseElementsComputed
    (source : PeriodicCNF Nat) : List (GreenElement RoutedVariable) :=
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
