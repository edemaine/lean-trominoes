/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCarrierLookupSemantics
import LeanTrominoes.RetainedAngularFanFinalCarrierNormalizedDirectionData
import LeanTrominoes.RetainedAngularFanFinalCarrierRouteGeometry
import LeanTrominoes.RetainedAngularFanFinalCarrierScaledTerminalGeometry
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

/-- The positively scaled source route addressed by an indexed final
carrier. -/
abbrev finalCarrierIndexedScaledRoute
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (clauseIndex : Nat)
    (literalIndex : Fin 2) : List Cell :=
  scalePolyline retainedAngularFanSourceClearanceFactor
    (finalCoordinatedSourceRoutes
      (PeriodicThreeSATThree.formula source) clauseIndex literalIndex)

/-- The public normalized direction word addressed by an indexed final
carrier. -/
def finalCarrierIndexedPublicDirectionWord
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (clauseIndex : Nat)
    (literalIndex : Fin 2) : List AxisDirection :=
  Gadget.unitSubdivisionDirections
    (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
      (PeriodicThreeSATThree.formula source) clauseIndex literalIndex)

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
abbrev scaledRoute
    {Variable : Type} [DecidableEq Variable]
    (occurrence : FinalCarrierIndexedOccurrence Variable) : List Cell :=
  finalCarrierIndexedScaledRoute occurrence.source occurrence.clauseIndex
    occurrence.literalIndex

/-- The exact scaled semantic terminal datum addressed by this occurrence. -/
abbrev scaledTerminalData
    {Variable : Type} [DecidableEq Variable]
    (occurrence : FinalCarrierIndexedOccurrence Variable) :
    RetainedTerminalData :=
  finalCarrierActualScaledTerminalData occurrence.source
    occurrence.taggedLink occurrence.literalIndex

/-- The exact scaled semantic prefix word addressed by this occurrence. -/
abbrev scaledPrefixDirections
    {Variable : Type} [DecidableEq Variable]
    (occurrence : FinalCarrierIndexedOccurrence Variable) :
    List AxisDirection :=
  finalCarrierActualScaledPrefixDirections occurrence.source
    occurrence.taggedLink occurrence.literalIndex

/-- The final occurrence slot used by this carrier route. -/
abbrev slot
    {Variable : Type} [DecidableEq Variable]
    (occurrence : FinalCarrierIndexedOccurrence Variable) :
    RetainedTerminalSlot :=
  retainedFinalCoordinatedOccurrenceSlot occurrence.retained
    occurrence.literal occurrence.clauseIndex occurrence.literalIndex

/-- The packaged public-to-semantic direction equality at this occurrence. -/
abbrev PublicDirectionsEqSemanticModel
    {Variable : Type} [DecidableEq Variable]
    (occurrence : FinalCarrierIndexedOccurrence Variable) : Prop :=
  let retained := PeriodicThreeSATThree.formula occurrence.source
  let localClauseIndex := if occurrence.taggedLink.2 then 0 else 1
  let route :=
    scalePolyline retainedAngularFanSourceClearanceFactor
      (finalCoordinatedSourceRoutes retained occurrence.clauseIndex
        occurrence.literalIndex)
  let terminal :=
    scaleRetainedTerminalData retainedAngularFanSourceClearanceFactor
      (carrierLensRouteTerminalData
        occurrence.taggedLink.1.first.isHorizontal
        (AxisDirection.axisSpan
          (CarrierNode.position retained.incidenceGraph
            occurrence.taggedLink.1.first)
          (CarrierNode.position retained.incidenceGraph
            occurrence.taggedLink.1.second))
        localClauseIndex occurrence.literalIndex)
  let slot := retainedFinalCoordinatedOccurrenceSlot retained
    occurrence.literal occurrence.clauseIndex occurrence.literalIndex
  Gadget.unitSubdivisionDirections
      (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
        retained occurrence.clauseIndex occurrence.literalIndex) =
    Gadget.unitSubdivisionDirections
      (AxisDirection.normalizeOrthogonalPolyline
        ((CarrierFallbackRouteTailRecords.routeKind localClauseIndex
            occurrence.literalIndex).splicedOwnFigure7Route
          route terminal slot))

/-- The four packaged facts at this indexed occurrence. -/
abbrev ScaledRouteEvidence
    {Variable : Type} [DecidableEq Variable]
    (occurrence : FinalCarrierIndexedOccurrence Variable) : Prop :=
  FinalCarrierScaledRouteEvidence
    (scalePolyline retainedAngularFanSourceClearanceFactor
      (finalCoordinatedSourceRoutes
        (PeriodicThreeSATThree.formula occurrence.source)
        occurrence.clauseIndex occurrence.literalIndex))
    (scaleRetainedTerminalData retainedAngularFanSourceClearanceFactor
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
        occurrence.literalIndex))
    (Gadget.repeatDirections 1152
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
        occurrence.literalIndex))

/-- The two proved route consequences carried separately from the original
lookup package. -/
structure RouteDirectionEvidence
    {Variable : Type} [DecidableEq Variable]
    (occurrence : FinalCarrierIndexedOccurrence Variable) : Prop where
  routeEvidence : occurrence.ScaledRouteEvidence
  publicDirectionsEvidence : occurrence.PublicDirectionsEqSemanticModel

/-- Terminal classification transported to the finite carrier geometry. -/
structure GeometryRouteClassified
    {Variable : Type} [DecidableEq Variable]
    (occurrence : FinalCarrierIndexedOccurrence Variable)
    (nextSlice : Bool) : Prop where
  evidence : FinalCarrierGeometryClassification
        (scalePolyline retainedAngularFanSourceClearanceFactor
          (finalCoordinatedSourceRoutes
            (PeriodicThreeSATThree.formula occurrence.source)
            occurrence.clauseIndex occurrence.literalIndex))
        (finalCarrierRouteGeometryAt occurrence.source occurrence.taggedLink
          nextSlice)
        (finalCarrierLocalClauseIndex occurrence.taggedLink)
        occurrence.literalIndex

/-- Prefix directions transported to the finite carrier geometry. -/
structure GeometryRoutePrefixDirections
    {Variable : Type} [DecidableEq Variable]
    (occurrence : FinalCarrierIndexedOccurrence Variable)
    (nextSlice : Bool) : Prop where
  prefixDirections : Gadget.unitSubdivisionDirections
      (retainedFallbackSourcePrefix
        (scalePolyline retainedAngularFanSourceClearanceFactor
          (finalCoordinatedSourceRoutes
            (PeriodicThreeSATThree.formula occurrence.source)
            occurrence.clauseIndex occurrence.literalIndex))) =
    Gadget.repeatDirections 1152
      (carrierLensRoutePrefixDirections
        (finalCarrierRouteGeometryAt occurrence.source
          occurrence.taggedLink nextSlice).horizontal
        (finalCarrierRouteGeometryAt occurrence.source
          occurrence.taggedLink nextSlice).span
        (finalCarrierLocalClauseIndex occurrence.taggedLink)
        occurrence.literalIndex)

/-- The compiler equality in the finite geometry coordinates used by the
generic extensionality theorem. -/
structure GeometryModelDirections
    {Variable : Type} [DecidableEq Variable]
    (occurrence : FinalCarrierIndexedOccurrence Variable)
    (nextSlice : Bool) : Prop where
  directions : Gadget.unitSubdivisionDirections
      (AxisDirection.normalizeOrthogonalPolyline
        ((CarrierFallbackRouteTailRecords.routeKind
              (finalCarrierLocalClauseIndex occurrence.taggedLink)
              occurrence.literalIndex).splicedOwnFigure7Route
          (scalePolyline retainedAngularFanSourceClearanceFactor
            (finalCoordinatedSourceRoutes
              (PeriodicThreeSATThree.formula occurrence.source)
              occurrence.clauseIndex occurrence.literalIndex))
          (scaleRetainedTerminalData retainedAngularFanSourceClearanceFactor
            (carrierLensRouteTerminalData
              (finalCarrierRouteGeometryAt occurrence.source
                occurrence.taggedLink nextSlice).horizontal
              (finalCarrierRouteGeometryAt occurrence.source
                occurrence.taggedLink nextSlice).span
              (finalCarrierLocalClauseIndex occurrence.taggedLink)
              occurrence.literalIndex))
          occurrence.slot)) =
    CarrierNormalizedFallbackRouteTailRecords.routeDirections
      (finalCarrierRouteGeometryAt occurrence.source
        occurrence.taggedLink nextSlice)
      (finalCarrierLocalClauseIndex occurrence.taggedLink)
      occurrence.literalIndex occurrence.slot

/-- The exact finite compiler direction claim for the semantic carrier-route
model at this occurrence. -/
def SemanticModelDirections
    {Variable : Type} [DecidableEq Variable]
    (occurrence : FinalCarrierIndexedOccurrence Variable)
    (nextSlice : Bool) : Prop :=
  finalCarrierNamedSemanticModelDirections occurrence.source
    occurrence.taggedLink nextSlice occurrence.literalIndex occurrence.slot
    occurrence.scaledRoute occurrence.scaledTerminalData

/-- The compact public-to-compiler direction claim at this occurrence. -/
def PublicDirections
    {Variable : Type} [DecidableEq Variable]
    (occurrence : FinalCarrierIndexedOccurrence Variable)
    (nextSlice : Bool) : Prop :=
  let retained := PeriodicThreeSATThree.formula occurrence.source
  let slot := retainedFinalCoordinatedOccurrenceSlot retained
    occurrence.literal occurrence.clauseIndex occurrence.literalIndex
  Gadget.unitSubdivisionDirections
      (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
        retained occurrence.clauseIndex occurrence.literalIndex) =
    finalCarrierModelDirectionWord occurrence.source occurrence.taggedLink
      nextSlice occurrence.literalIndex slot

/-- The compact normalization request at this occurrence. -/
structure NormalizationRequest
    {Variable : Type} [DecidableEq Variable]
    (occurrence : FinalCarrierIndexedOccurrence Variable)
    (nextSlice : Bool) : Prop where
  spanLarge :
    8 ≤ (finalCarrierRouteGeometryAt occurrence.source
      occurrence.taggedLink nextSlice).span
  evidence : occurrence.RouteDirectionEvidence

end FinalCarrierIndexedOccurrence
end PeriodicEightOccurrenceSplit
end LeanTrominoes
