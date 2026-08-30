/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCarrierRawRoutePrefixDirectionSemantics
import LeanTrominoes.RetainedAngularFanFinalCarrierScaledClassification
import LeanTrominoes.RetainedAngularFanFinalCarrierIndexedOccurrence
import LeanTrominoes.RetainedAngularFanFinalCarrierScaledOrthogonality
import LeanTrominoes.RetainedAngularFanFinalCarrierScaledRouteEvidenceData
import LeanTrominoes.RetainedAngularFanFinalThreeSATThreeScaledRouteLength

/-! # Collected scaled-route evidence for final retained carriers -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing PlanarThreeSAT
open PeriodicThreeSATThree

local instance finalCarrierScaledEvidenceThreeOccurrenceDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq (ThreeOccurrenceVariable Variable) :=
  fiveFamilyNormalizedThreeOccurrenceDecidableEq

/-- Indexed carrier membership supplies all four source-side facts. -/
theorem finalCarrierScaledRoute_evidence
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
      finalCarrierTaggedLinkIndexed source taggedLink clauseIndex)
    {clause : PositionedPeriodicClause
      (WrappedPeriodicPlanarSATVariable
        (ThreeOccurrenceVariable Variable))}
    (clauseMember :
      (clause, clauseIndex) ∈
        (finalCoordinatedSource
          (PeriodicThreeSATThree.formula source)).clauses.zipIdx)
    {literal : PeriodicLiteral
      (WrappedPeriodicPlanarSATVariable
        (ThreeOccurrenceVariable Variable))}
    (literalIndex : Fin 2)
    (literalMember :
      (literal, literalIndex.val) ∈ clause.literals.zipIdx) :
    FinalCarrierScaledRouteEvidence
      (scalePolyline retainedAngularFanSourceClearanceFactor
        (finalCoordinatedSourceRoutes
          (PeriodicThreeSATThree.formula source)
          clauseIndex literalIndex))
      (scaleRetainedTerminalData
        retainedAngularFanSourceClearanceFactor
        (carrierLensRouteTerminalData taggedLink.1.first.isHorizontal
          (AxisDirection.axisSpan
            (CarrierNode.position
              (PeriodicThreeSATThree.formula source).incidenceGraph
              taggedLink.1.first)
            (CarrierNode.position
              (PeriodicThreeSATThree.formula source).incidenceGraph
              taggedLink.1.second))
          (if taggedLink.2 then 0 else 1) literalIndex))
      (Gadget.repeatDirections 1152
        (carrierLensRoutePrefixDirections taggedLink.1.first.isHorizontal
          (AxisDirection.axisSpan
            (CarrierNode.position
              (PeriodicThreeSATThree.formula source).incidenceGraph
              taggedLink.1.first)
            (CarrierNode.position
              (PeriodicThreeSATThree.formula source).incidenceGraph
              taggedLink.1.second))
          (if taggedLink.2 then 0 else 1) literalIndex)) := by
  exact ⟨
    finalCoordinatedScaledThreeSATThreeSourceRoute_length_ge_two
      source sourceLocal sourceWidth sourceClausesNonempty
      clauseMember literalMember,
    finalCoordinatedScaledCarrierSourceRoute_classified
      source sourceLocal sourceWidth sourceClausesNonempty positiveOffsets
      taggedLink clauseIndex taggedLinkIndexed clauseMember
      literalIndex literalMember,
    finalCoordinatedScaledCarrierSourceRoute_orthogonal
      source sourceLocal sourceWidth sourceClausesNonempty positiveOffsets
      taggedLink clauseIndex taggedLinkIndexed clauseMember
      literalIndex literalMember,
    finalCarrierFallbackSourcePrefix_directions_eq
      source sourceLocal sourceWidth sourceClausesNonempty positiveOffsets
      taggedLink clauseIndex taggedLinkIndexed literalIndex⟩

/-- The indexed-occurrence package supplies its four scaled-route facts. -/
theorem FinalCarrierIndexedOccurrence.scaledRouteEvidence
    {Variable : Type} [DecidableEq Variable]
    (occurrence : FinalCarrierIndexedOccurrence Variable) :
    FinalCarrierScaledRouteEvidence occurrence.scaledRoute
      occurrence.scaledTerminalData occurrence.scaledPrefixDirections :=
  finalCarrierScaledRoute_evidence
    occurrence.source occurrence.sourceLocal occurrence.sourceWidth
    occurrence.sourceClausesNonempty occurrence.positiveOffsets
    occurrence.taggedLink occurrence.clauseIndex
    occurrence.taggedLinkIndexed occurrence.clauseMember
    occurrence.literalIndex occurrence.literalMember

end PeriodicEightOccurrenceSplit
end LeanTrominoes
