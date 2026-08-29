/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalBendTerminalDataSemantics
import LeanTrominoes.RetainedAngularOccurrenceTerminalCoordinate
import LeanTrominoes.RetainedAngularCarrierTerminalCoordinateData

/-! # Actual final terminal coordinates of retained bends -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing
open PeriodicThreeSATThree

local instance finalBendCoordinateThreeOccurrenceDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq (ThreeOccurrenceVariable Variable) :=
  fiveFamilyNormalizedThreeOccurrenceDecidableEq

/-- At a globally indexed final bend incidence, the terminal coordinate is
the coordinate of the corresponding canonical corner-table datum. -/
theorem finalBendOccurrenceTerminalCoordinate_eq
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceClausesNonempty : ∀ clause ∈ source.clauses, clause ≠ [])
    (positiveOffsets : ∀ incidence ∈ occurrenceIncidences source,
      incidence.edge.offset = (0, 0) ∨
        incidence.edge.offset = (1, 0))
    (taggedBend : RouteBend × Bool)
    (clauseIndex : Nat)
    (taggedBendIndexed :
      finalBendTaggedBendIndexed source taggedBend clauseIndex)
    (atom : WrappedPeriodicPlanarSATVariable
      (ThreeOccurrenceVariable Variable))
    (literalIndex : Nat) :
    ofLex (retainedOccurrenceTerminalCoordinate
        (finalCoordinatedSourceRoutes
          (PeriodicThreeSATThree.formula source))
        (atom, clauseIndex, literalIndex)) =
      retainedTerminalDataCoordinate
        (finalBendSemanticTerminalDataAt
          source taggedBend literalIndex) := by
  change retainedTerminalDataCoordinate
      (finalBendActualTerminalDataAt
        source clauseIndex literalIndex) = _
  exact congrArg retainedTerminalDataCoordinate
    (finalBendTerminalData_eq
      source sourceLocal sourceWidth sourceClausesNonempty
        positiveOffsets taggedBend clauseIndex
          taggedBendIndexed literalIndex)

end PeriodicEightOccurrenceSplit
end LeanTrominoes
