/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierRawRepresentativeRouteSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataFallbackPrefixDirectionWords
import LeanTrominoes.RetainedAngularFanFallbackSourcePrefixDirectionData
import LeanTrominoes.RetainedAngularFanFinalCarrierLookupSemantics
import LeanTrominoes.RetainedAngularFanFinalCoordinatedRawRoutePrefixDirections

/-! # Raw prefix words of final retained-carrier routes -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing PlanarThreeSAT
open PeriodicThreeSATThree

local instance finalCarrierRawPrefixThreeOccurrenceDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq (ThreeOccurrenceVariable Variable) :=
  fiveFamilyNormalizedThreeOccurrenceDecidableEq

/-- At an indexed final carrier occurrence, deleting the old variable
endpoint exposes the explicit equality-lens prefix word. -/
theorem finalCoordinatedSourceCarrierRoute_prefixDirections_eq
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
    (literalIndex : Nat) :
    let retained := PeriodicThreeSATThree.formula source
    let localClauseIndex := if taggedLink.2 then 0 else 1
    Gadget.unitSubdivisionDirections
        (finalCoordinatedSourceRoutes retained
          clauseIndex literalIndex).dropLast =
      carrierLensRoutePrefixDirections taggedLink.1.first.isHorizontal
        (AxisDirection.axisSpan
          (CarrierNode.position retained.incidenceGraph taggedLink.1.first)
          (CarrierNode.position retained.incidenceGraph taggedLink.1.second))
        localClauseIndex literalIndex := by
  dsimp only
  let retained := PeriodicThreeSATThree.formula source
  let localClauseIndex := if taggedLink.2 then 0 else 1
  have lookups := finalCarrierClause_metadata_lookups
    source sourceLocal sourceWidth sourceClausesNonempty positiveOffsets
      taggedLink clauseIndex taggedLinkIndexed
  have taggedLinkMember : taggedLink ∈
      (retainedDrawingCompleteCarrierLinks
        retained.incidenceGraph).product [true, false] :=
    List.fst_mem_of_mem_zipIdx taggedLinkIndexed
  have linkMember : taggedLink.1 ∈
      retainedDrawingCompleteCarrierLinks retained.incidenceGraph :=
    (List.mem_product.mp taggedLinkMember).1
  have retainedWellFormed : retained.incidenceGraph.IsWellFormed :=
    formula_incidenceGraph_isWellFormed source
  have retainedDegree : retained.incidenceGraph.DegreeAtMost 3 :=
    formula_incidenceGraph_degreeAtMostThree sourceWidth
  have retainedLocal : retained.incidenceGraph.IsLocal :=
    formula_incidenceGraph_isLocal sourceLocal
  calc
    Gadget.unitSubdivisionDirections
          (finalCoordinatedSourceRoutes retained
            clauseIndex literalIndex).dropLast =
        Gadget.unitSubdivisionDirections
          (rawRepresentativeRoute retained
            clauseIndex literalIndex).dropLast :=
      finalCoordinatedSourceRoutes_prefixDirections_eq_rawRepresentativeRoute
        retained clauseIndex literalIndex
    _ = Gadget.unitSubdivisionDirections
          ((((DrawingPlanarSATClauseSource.carrier
              taggedLink.1 localClauseIndex).incidenceDrawing retained).routes
            localClauseIndex literalIndex).dropLast) := by
      rw [rawRepresentativeRoute_eq_carrierClauseMetadataAt
        retained taggedLink clauseIndex literalIndex lookups.1 lookups.2]
    _ = _ := carrier_routePrefixDirections_eq
      retained retainedWellFormed retainedDegree retainedLocal
        taggedLink.1 linkMember localClauseIndex literalIndex

/-- After the construction's two fixed source refinements, the final carrier
fallback prefix is the exact 1152-fold compiler prefix word. -/
theorem finalCarrierFallbackSourcePrefix_directions_eq
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
    (literalIndex : Nat) :
    let retained := PeriodicThreeSATThree.formula source
    let localClauseIndex := if taggedLink.2 then 0 else 1
    Gadget.unitSubdivisionDirections
        (retainedFallbackSourcePrefix
          (scalePolyline retainedAngularFanSourceClearanceFactor
            (finalCoordinatedSourceRoutes retained
              clauseIndex literalIndex))) =
      Gadget.repeatDirections 1152
        (carrierLensRoutePrefixDirections
          taggedLink.1.first.isHorizontal
          (AxisDirection.axisSpan
            (CarrierNode.position retained.incidenceGraph taggedLink.1.first)
            (CarrierNode.position retained.incidenceGraph taggedLink.1.second))
          localClauseIndex literalIndex) := by
  dsimp only
  rw [retainedFallbackSourcePrefix_sourceClearanceScaled_directions,
    finalCoordinatedSourceCarrierRoute_prefixDirections_eq
      source sourceLocal sourceWidth sourceClausesNonempty positiveOffsets
        taggedLink clauseIndex taggedLinkIndexed literalIndex]

end PeriodicEightOccurrenceSplit
end LeanTrominoes
