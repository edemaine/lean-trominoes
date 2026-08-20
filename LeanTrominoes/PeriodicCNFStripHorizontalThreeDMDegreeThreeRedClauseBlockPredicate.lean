/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMDegreeThreeRedClauseBlockData
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMTerminalOccurrenceCounts

/-! # Red degree-three filter on one clause block -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  horizontalThreeDMTripleVariableDecidableEq

theorem horizontalThreeDMRedClauseBlock_filter_of_arity
    (typed : PeriodicCNF RoutedVariable)
    (occurrences : typed.OccurrencesAtMost 3)
    (tagged : PeriodicClause RoutedVariable × Nat)
    (clauseLookup : typed.clauses[tagged.2]? = some tagged.1)
    (arity : tagged.1.length = 2 ∨ tagged.1.length = 3) :
    ([RedElement.clauseInternal tagged.2] ++
        allTerminalGroups.map
          (RedElement.clauseTerminal tagged.2)).filter
        (horizontalThreeDMRedElementDegreeThree typed) =
      [.clauseInternal tagged.2,
        .clauseTerminal tagged.2 .top,
        .clauseTerminal tagged.2 .left] ++
        if tagged.1.length = 3 then
          [.clauseTerminal tagged.2 .right]
        else [] := by
  have topCount :=
    terminalOccurrenceEnumeration_length_of_arity
      typed occurrences tagged.2 tagged.1 clauseLookup arity .top
  have leftCount :=
    terminalOccurrenceEnumeration_length_of_arity
      typed occurrences tagged.2 tagged.1 clauseLookup arity .left
  have rightCount :=
    terminalOccurrenceEnumeration_length_of_arity
      typed occurrences tagged.2 tagged.1 clauseLookup arity .right
  rcases arity with lengthTwo | lengthThree
  · simp [horizontalThreeDMRedElementDegreeThree, allTerminalGroups,
      topCount, leftCount, rightCount, lengthTwo]
  · simp [horizontalThreeDMRedElementDegreeThree, allTerminalGroups,
      topCount, leftCount, rightCount, lengthThree]

end PeriodicCNFStripReduction
end LeanTrominoes
