/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMDegreeThreeBlueClauseData
import LeanTrominoes.PeriodicCNFStripDirectSparseAffineVertexRequestTripleIndexed

/-! # Indexed blue clause-element blocks -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  horizontalThreeDMTripleVariableDecidableEq

def horizontalThreeDMBlueClauseElementsZippedComputed
    (source : PeriodicCNF Nat) : List (BlueElement RoutedVariable) :=
  let typed := horizontalThreeDMTypedSourceComputed source
  typed.clauses.zipIdx.flatMap fun tagged =>
    [.clauseInternal tagged.2] ++
      allTerminalGroups.map (BlueElement.clauseTerminal tagged.2)

theorem horizontalThreeDMBlueClauseElementsComputed_eq_zipped
    (source : PeriodicCNF Nat) :
    horizontalThreeDMBlueClauseElementsComputed source =
      horizontalThreeDMBlueClauseElementsZippedComputed source := by
  unfold horizontalThreeDMBlueClauseElementsComputed
    horizontalThreeDMBlueClauseElementsZippedComputed
  exact range_getD_flatMap_eq_zipIdx
    (horizontalThreeDMTypedSourceComputed source).clauses []
    (fun (_clause : PeriodicClause RoutedVariable) clauseIndex =>
      [BlueElement.clauseInternal clauseIndex] ++
        allTerminalGroups.map
          (BlueElement.clauseTerminal clauseIndex))

def horizontalThreeDMBlueDegreeThreeClauseElementsComputed
    (source : PeriodicCNF Nat) : List (BlueElement RoutedVariable) :=
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
