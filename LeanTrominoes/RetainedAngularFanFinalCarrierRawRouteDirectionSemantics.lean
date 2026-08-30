/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierRawRepresentativeRouteSemantics
import LeanTrominoes.RetainedAngularFanFinalCarrierLookupSemantics
import LeanTrominoes.RetainedAngularFanFinalCoordinatedRawRouteDirections

/-! # Raw direction words of final retained-carrier routes -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing PlanarThreeSAT
open PeriodicThreeSATThree

local instance finalCarrierRawRouteThreeOccurrenceDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq (ThreeOccurrenceVariable Variable) :=
  fiveFamilyNormalizedThreeOccurrenceDecidableEq

/-- The final coordinated source route at a retained-carrier occurrence has
the explicit complete equality-lens direction word. -/
theorem finalCoordinatedSourceCarrierRoute_directions_eq
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
        (finalCoordinatedSourceRoutes retained clauseIndex literalIndex) =
      carrierLensRouteDirections taggedLink.1.first.isHorizontal
        (AxisDirection.axisSpan
          (CarrierNode.position retained.incidenceGraph taggedLink.1.first)
          (CarrierNode.position retained.incidenceGraph taggedLink.1.second))
        localClauseIndex literalIndex := by
  dsimp only
  let retained := PeriodicThreeSATThree.formula source
  have lookups := finalCarrierClause_metadata_lookups
    source sourceLocal sourceWidth sourceClausesNonempty positiveOffsets
      taggedLink clauseIndex taggedLinkIndexed
  have taggedLinkMember : taggedLink ∈
      (retainedDrawingCompleteCarrierLinks
        retained.incidenceGraph).product [true, false] :=
    List.fst_mem_of_mem_zipIdx taggedLinkIndexed
  have retainedWellFormed : retained.incidenceGraph.IsWellFormed :=
    formula_incidenceGraph_isWellFormed source
  have retainedDegree : retained.incidenceGraph.DegreeAtMost 3 :=
    formula_incidenceGraph_degreeAtMostThree sourceWidth
  have retainedLocal : retained.incidenceGraph.IsLocal :=
    formula_incidenceGraph_isLocal sourceLocal
  calc
    Gadget.unitSubdivisionDirections
          (finalCoordinatedSourceRoutes retained clauseIndex literalIndex) =
        Gadget.unitSubdivisionDirections
          (rawRepresentativeRoute retained clauseIndex literalIndex) :=
      finalCoordinatedSourceRoutes_directions_eq_rawRepresentativeRoute
        retained clauseIndex literalIndex
    _ = _ := rawRepresentativeRoute_carrier_directions_eq
      retained retainedWellFormed retainedDegree retainedLocal
        taggedLink taggedLinkMember clauseIndex literalIndex
        lookups.1 lookups.2

end PeriodicEightOccurrenceSplit
end LeanTrominoes
