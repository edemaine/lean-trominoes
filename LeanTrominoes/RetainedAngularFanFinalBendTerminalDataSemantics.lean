/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalBendTerminalVectorSemantics

/-! # Actual final terminal data of retained bends -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicThreeSATThree

local instance finalBendTerminalThreeOccurrenceDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq (ThreeOccurrenceVariable Variable) :=
  fiveFamilyNormalizedThreeOccurrenceDecidableEq

/-- Actual classified terminal datum at one final bend incidence. -/
def finalBendActualTerminalDataAt
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (clauseIndex literalIndex : Nat) : RetainedTerminalData :=
  classifiedRetainedTerminalData
    (finalBendActualTerminalVectorAt source clauseIndex literalIndex)

/-- Every globally indexed canonical bend clause uses its exact local
corner-table terminal datum. -/
theorem finalBendTerminalData_eq
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceClausesNonempty : ∀ clause ∈ source.clauses, clause ≠ [])
    (positiveOffsets : ∀ incidence ∈ occurrenceIncidences source,
      incidence.edge.offset = (0, 0) ∨
        incidence.edge.offset = (1, 0))
    (taggedBend : PeriodicOrthocrossing.RouteBend × Bool)
    (clauseIndex : Nat)
    (taggedBendIndexed :
      finalBendTaggedBendIndexed source taggedBend clauseIndex)
    (literalIndex : Nat) :
    finalBendActualTerminalDataAt source clauseIndex literalIndex =
      finalBendSemanticTerminalDataAt source taggedBend literalIndex := by
  unfold finalBendActualTerminalDataAt
  calc
    classifiedRetainedTerminalData
          (finalBendActualTerminalVectorAt
            source clauseIndex literalIndex) =
        classifiedRetainedTerminalData
          (finalBendRawRepresentativeTerminalVectorAt
            source clauseIndex literalIndex) :=
      congrArg classifiedRetainedTerminalData
        (finalBendActualTerminalVector_eq_rawRepresentative
          source clauseIndex literalIndex)
    _ = finalBendSemanticTerminalDataAt
          source taggedBend literalIndex :=
      finalBendRawTerminalData_eq_semantic
        source sourceLocal sourceWidth sourceClausesNonempty
          positiveOffsets taggedBend clauseIndex
            taggedBendIndexed literalIndex

end PeriodicEightOccurrenceSplit
end LeanTrominoes
