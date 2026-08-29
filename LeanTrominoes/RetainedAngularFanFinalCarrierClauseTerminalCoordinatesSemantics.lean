/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCarrierTerminalCoordinateSemantics

/-! # Terminal-coordinate blocks of final retained carrier clauses -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing PlanarThreeSAT
open PeriodicThreeSATThree

local instance finalCarrierClauseCoordinateThreeOccurrenceDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq (ThreeOccurrenceVariable Variable) :=
  fiveFamilyNormalizedThreeOccurrenceDecidableEq

/-- One normalized carrier implication contributes its two semantic
carrier-lens coordinates in literal order. -/
theorem finalCarrierClauseTerminalCoordinates_eq
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceClausesNonempty : ∀ clause ∈ source.clauses, clause ≠ [])
    (positiveOffsets : ∀ incidence ∈ occurrenceIncidences source,
      incidence.edge.offset = (0, 0) ∨
        incidence.edge.offset = (1, 0))
    (taggedLink : EqualityLink CarrierNode × Bool)
    (clauseIndex : Nat)
    (taggedLinkIndexed :
      finalCarrierTaggedLinkIndexed source taggedLink clauseIndex) :
    (normalizedCarrierClauseAt
        (PeriodicThreeSATThree.formula source) taggedLink).zipIdx.map
        (fun taggedLiteral =>
          ofLex (retainedOccurrenceTerminalCoordinate
            (finalCoordinatedSourceRoutes
              (PeriodicThreeSATThree.formula source))
            (taggedLiteral.1.atom, clauseIndex,
              taggedLiteral.2))) =
      [retainedTerminalDataCoordinate
          (carrierLensRouteTerminalDataTagged
            taggedLink.1.first.isHorizontal
            (AxisDirection.axisSpan
              (CarrierNode.position
                (PeriodicThreeSATThree.formula source).incidenceGraph
                  taggedLink.1.first)
              (CarrierNode.position
                (PeriodicThreeSATThree.formula source).incidenceGraph
                  taggedLink.1.second))
            taggedLink.2 0),
        retainedTerminalDataCoordinate
          (carrierLensRouteTerminalDataTagged
            taggedLink.1.first.isHorizontal
            (AxisDirection.axisSpan
              (CarrierNode.position
                (PeriodicThreeSATThree.formula source).incidenceGraph
                  taggedLink.1.first)
              (CarrierNode.position
                (PeriodicThreeSATThree.formula source).incidenceGraph
                  taggedLink.1.second))
            taggedLink.2 1)] := by
  have coordinateEq
      (atom : WrappedPeriodicPlanarSATVariable
        (ThreeOccurrenceVariable Variable))
      (literalIndex : Nat) :=
    finalCarrierOccurrenceTerminalCoordinate_eq
      source sourceLocal sourceWidth sourceClausesNonempty
        positiveOffsets taggedLink clauseIndex taggedLinkIndexed
          atom literalIndex
  rcases taggedLink with ⟨link, direction⟩
  cases direction <;>
    simp [normalizedCarrierClauseAt,
      PeriodicEquality.normalizedClause,
      PeriodicEquality.normalizeLink, coordinateEq]

end PeriodicEightOccurrenceSplit
end LeanTrominoes
