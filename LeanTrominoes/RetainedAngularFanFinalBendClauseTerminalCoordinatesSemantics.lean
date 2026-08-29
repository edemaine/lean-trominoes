/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalBendTerminalCoordinateSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataTaggedBendTerminalData

/-! # Terminal-coordinate blocks of final retained bend clauses -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing PlanarThreeSAT
open PeriodicThreeSATThree

local instance finalBendClauseCoordinateThreeOccurrenceDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq (ThreeOccurrenceVariable Variable) :=
  fiveFamilyNormalizedThreeOccurrenceDecidableEq

/-- One normalized bend implication contributes its two semantic corner-table
coordinates in literal order. -/
theorem finalBendClauseTerminalCoordinates_eq
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
      finalBendTaggedBendIndexed source taggedBend clauseIndex) :
    (normalizedBendClauseAt
        (PeriodicThreeSATThree.formula source) taggedBend).zipIdx.map
        (fun taggedLiteral =>
          ofLex (retainedOccurrenceTerminalCoordinate
            (finalCoordinatedSourceRoutes
              (PeriodicThreeSATThree.formula source))
            (taggedLiteral.1.atom, clauseIndex,
              taggedLiteral.2))) =
      [retainedTerminalDataCoordinate
          (bendRouteTerminalDataTagged
            taggedBend.1.incomingPort taggedBend.1.outgoingPort
            taggedBend.2 0),
        retainedTerminalDataCoordinate
          (bendRouteTerminalDataTagged
            taggedBend.1.incomingPort taggedBend.1.outgoingPort
            taggedBend.2 1)] := by
  have coordinateEq
      (atom : WrappedPeriodicPlanarSATVariable
        (ThreeOccurrenceVariable Variable))
      (literalIndex : Nat) :=
    finalBendOccurrenceTerminalCoordinate_eq
      source sourceLocal sourceWidth sourceClausesNonempty
        positiveOffsets taggedBend clauseIndex taggedBendIndexed
          atom literalIndex
  rcases taggedBend with ⟨routeBend, direction⟩
  cases direction <;>
    simp [normalizedBendClauseAt,
      PeriodicEquality.normalizedClause, coordinateEq,
      finalBendSemanticTerminalDataAt,
      bendRouteTerminalDataTagged]

end PeriodicEightOccurrenceSplit
end LeanTrominoes
