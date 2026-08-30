/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCarrierLookupSemantics
import LeanTrominoes.RetainedAngularFanFinalCarrierNormalizedDirectionData
import LeanTrominoes.RetainedAngularFanFinalCarrierRouteGeometry
import LeanTrominoes.RetainedAngularFanFinalCarrierScaledRouteEvidenceData
import LeanTrominoes.RetainedAngularFanFinalCoordinatedRoutes

/-! # Indexed final retained-carrier occurrences -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing PlanarThreeSAT
open PeriodicThreeSATThree

local instance finalCarrierIndexedOccurrenceThreeOccurrenceDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq (ThreeOccurrenceVariable Variable) :=
  fiveFamilyNormalizedThreeOccurrenceDecidableEq

/-- All source hypotheses and lookup witnesses for one genuine literal of an
indexed final retained-carrier clause. -/
structure FinalCarrierIndexedOccurrence
    (Variable : Type) [DecidableEq Variable] where
  source : PeriodicCNF Variable
  sourceLocal : source.IsLocal
  sourceWidth : source.WidthAtMost 3
  sourceClausesNonempty : ∀ clause ∈ source.clauses, clause ≠ []
  positiveOffsets : ∀ incidence ∈ occurrenceIncidences source,
    incidence.edge.offset = (0, 0) ∨ incidence.edge.offset = (1, 0)
  taggedLink : EqualityLink CarrierNode × Bool
  clauseIndex : Nat
  taggedLinkIndexed :
    finalCarrierTaggedLinkIndexed source taggedLink clauseIndex
  clause : PositionedPeriodicClause
    (WrappedPeriodicPlanarSATVariable
      (ThreeOccurrenceVariable Variable))
  clauseMember :
    (clause, clauseIndex) ∈
      (finalCoordinatedSource
        (PeriodicThreeSATThree.formula source)).clauses.zipIdx
  literal : PeriodicLiteral
    (WrappedPeriodicPlanarSATVariable
      (ThreeOccurrenceVariable Variable))
  literalIndex : Fin 2
  literalMember :
    (literal, literalIndex.val) ∈ clause.literals.zipIdx

namespace FinalCarrierIndexedOccurrence

/-- The retained three-occurrence formula addressed by this occurrence. -/
def retained
    {Variable : Type} [DecidableEq Variable]
    (occurrence : FinalCarrierIndexedOccurrence Variable) :=
  PeriodicThreeSATThree.formula occurrence.source

/-- The positively scaled raw route addressed by this occurrence. -/
def scaledRoute
    {Variable : Type} [DecidableEq Variable]
    (occurrence : FinalCarrierIndexedOccurrence Variable) : List Cell :=
  scalePolyline retainedAngularFanSourceClearanceFactor
    (finalCoordinatedSourceRoutes occurrence.retained
      occurrence.clauseIndex occurrence.literalIndex)

/-- The exact scaled semantic terminal datum addressed by this occurrence. -/
def scaledTerminalData
    {Variable : Type} [DecidableEq Variable]
    (occurrence : FinalCarrierIndexedOccurrence Variable) :
    RetainedTerminalData :=
  scaleRetainedTerminalData retainedAngularFanSourceClearanceFactor
    (carrierLensRouteTerminalData
      occurrence.taggedLink.1.first.isHorizontal
      (AxisDirection.axisSpan
        (CarrierNode.position occurrence.retained.incidenceGraph
          occurrence.taggedLink.1.first)
        (CarrierNode.position occurrence.retained.incidenceGraph
          occurrence.taggedLink.1.second))
      (if occurrence.taggedLink.2 then 0 else 1)
      occurrence.literalIndex)

/-- The named terminal datum unfolds to its semantic carrier expression. -/
theorem scaledTerminalData_eq
    {Variable : Type} [DecidableEq Variable]
    (occurrence : FinalCarrierIndexedOccurrence Variable) :
    occurrence.scaledTerminalData =
      scaleRetainedTerminalData retainedAngularFanSourceClearanceFactor
        (carrierLensRouteTerminalData
          occurrence.taggedLink.1.first.isHorizontal
          (AxisDirection.axisSpan
            (CarrierNode.position
              (PeriodicThreeSATThree.formula occurrence.source).incidenceGraph
              occurrence.taggedLink.1.first)
            (CarrierNode.position
              (PeriodicThreeSATThree.formula occurrence.source).incidenceGraph
              occurrence.taggedLink.1.second))
          (if occurrence.taggedLink.2 then 0 else 1)
          occurrence.literalIndex) := rfl

/-- The exact scaled semantic prefix word addressed by this occurrence. -/
def scaledPrefixDirections
    {Variable : Type} [DecidableEq Variable]
    (occurrence : FinalCarrierIndexedOccurrence Variable) :
    List AxisDirection :=
  Gadget.repeatDirections 1152
    (carrierLensRoutePrefixDirections
      occurrence.taggedLink.1.first.isHorizontal
      (AxisDirection.axisSpan
        (CarrierNode.position occurrence.retained.incidenceGraph
          occurrence.taggedLink.1.first)
        (CarrierNode.position occurrence.retained.incidenceGraph
          occurrence.taggedLink.1.second))
      (if occurrence.taggedLink.2 then 0 else 1)
      occurrence.literalIndex)

/-- The named prefix word unfolds to its semantic carrier expression. -/
theorem scaledPrefixDirections_eq
    {Variable : Type} [DecidableEq Variable]
    (occurrence : FinalCarrierIndexedOccurrence Variable) :
    occurrence.scaledPrefixDirections =
      Gadget.repeatDirections 1152
        (carrierLensRoutePrefixDirections
          occurrence.taggedLink.1.first.isHorizontal
          (AxisDirection.axisSpan
            (CarrierNode.position
              (PeriodicThreeSATThree.formula occurrence.source).incidenceGraph
              occurrence.taggedLink.1.first)
            (CarrierNode.position
              (PeriodicThreeSATThree.formula occurrence.source).incidenceGraph
              occurrence.taggedLink.1.second))
          (if occurrence.taggedLink.2 then 0 else 1)
          occurrence.literalIndex) := rfl

/-- The final occurrence slot used by this carrier route. -/
def slot
    {Variable : Type} [DecidableEq Variable]
    (occurrence : FinalCarrierIndexedOccurrence Variable) :
    RetainedTerminalSlot :=
  retainedFinalCoordinatedOccurrenceSlot occurrence.retained
    occurrence.literal occurrence.clauseIndex occurrence.literalIndex

/-- The four packaged facts at this indexed occurrence. -/
def ScaledRouteEvidence
    {Variable : Type} [DecidableEq Variable]
    (occurrence : FinalCarrierIndexedOccurrence Variable) : Prop :=
  FinalCarrierScaledRouteEvidence occurrence.scaledRoute
    occurrence.scaledTerminalData occurrence.scaledPrefixDirections

/-- The exact finite compiler direction claim for the semantic carrier-route
model at this occurrence. -/
def SemanticModelDirections
    {Variable : Type} [DecidableEq Variable]
    (occurrence : FinalCarrierIndexedOccurrence Variable)
    (nextSlice : Bool) : Prop :=
  finalCarrierNamedSemanticModelDirections occurrence.source
    occurrence.taggedLink nextSlice occurrence.literalIndex
    occurrence.slot occurrence.scaledRoute occurrence.scaledTerminalData

/-- Occurrence-native normalization request containing only the two facts
that are not already named by the occurrence address. -/
structure NormalizationRequest
    {Variable : Type} [DecidableEq Variable]
    (occurrence : FinalCarrierIndexedOccurrence Variable)
    (nextSlice : Bool) : Prop where
  spanLarge :
    8 ≤ (finalCarrierRouteGeometryAt occurrence.source
      occurrence.taggedLink nextSlice).span
  routeEvidence : FinalCarrierScaledRouteEvidence occurrence.scaledRoute
    occurrence.scaledTerminalData occurrence.scaledPrefixDirections

end FinalCarrierIndexedOccurrence
end PeriodicEightOccurrenceSplit
end LeanTrominoes
