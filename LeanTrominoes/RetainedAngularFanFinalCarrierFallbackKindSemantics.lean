/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierFallbackKindSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierRawRepresentativeRouteSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRepresentativeRouteLength
import LeanTrominoes.PeriodicOrthocrossingCarrierFallbackRouteTailRecordBlockData
import LeanTrominoes.RetainedAngularFanFinalCarrierLookupSemantics
import LeanTrominoes.RetainedAngularFanFinalCarrierRouteGeometry
import LeanTrominoes.RetainedAngularFanFinalCoordinatedRoutes

/-! # Fallback policies of final retained-carrier routes -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing PlanarThreeSAT
open PeriodicThreeSATThree

local instance finalCarrierFallbackKindThreeOccurrenceDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq (ThreeOccurrenceVariable Variable) :=
  fiveFamilyNormalizedThreeOccurrenceDecidableEq

/-- The public singleton-prefix policy at an indexed final carrier occurrence
is exactly the finite carrier route-kind table. -/
theorem finalCoordinatedSourceCarrierRoute_fallbackKind_eq
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
    (if (finalCoordinatedSourceRoutes retained
          clauseIndex literalIndex).dropLast.length = 1 then
        RetainedFallbackFanKind.escaped
      else RetainedFallbackFanKind.ordinary) =
      CarrierFallbackRouteTailRecords.routeKind
        localClauseIndex literalIndex := by
  dsimp only
  let retained := PeriodicThreeSATThree.formula source
  let localClauseIndex := if taggedLink.2 then 0 else 1
  have lookups := finalCarrierClause_metadata_lookups
    source sourceLocal sourceWidth sourceClausesNonempty positiveOffsets
      taggedLink clauseIndex taggedLinkIndexed
  let localRoute :=
    ((DrawingPlanarSATClauseSource.carrier
        taggedLink.1 localClauseIndex).incidenceDrawing retained).routes
      localClauseIndex literalIndex
  have routeLengthEq :
      (finalCoordinatedSourceRoutes retained
        clauseIndex literalIndex).length = localRoute.length := by
    calc
      (finalCoordinatedSourceRoutes retained
          clauseIndex literalIndex).length =
          (rawRepresentativeRoute retained
            clauseIndex literalIndex).length :=
        incidenceRoutes_length_eq_rawRepresentativeRoute
          retained clauseIndex literalIndex
      _ = localRoute.length := congrArg List.length
        (rawRepresentativeRoute_eq_carrierClauseMetadataAt
          retained taggedLink clauseIndex literalIndex
            lookups.1 lookups.2)
  calc
    (if (finalCoordinatedSourceRoutes retained
          clauseIndex literalIndex).dropLast.length = 1 then
        RetainedFallbackFanKind.escaped
      else RetainedFallbackFanKind.ordinary) =
        (if localRoute.dropLast.length = 1 then
          RetainedFallbackFanKind.escaped
        else RetainedFallbackFanKind.ordinary) := by
      rw [List.length_dropLast, List.length_dropLast, routeLengthEq]
    _ = _ := by
      have singletonPrefix := carrier_route_singletonPrefix_iff
        retained taggedLink.1 localClauseIndex literalIndex
      cases taggedSide : taggedLink.2 <;>
        simp only [localRoute, localClauseIndex, taggedSide,
          Bool.false_eq_true,
          if_false, if_true] at singletonPrefix ⊢ <;>
        rcases literalIndex with (_ | _ | literalIndex) <;>
      simp_all [CarrierFallbackRouteTailRecords.routeKind]

/-- The same public policy equality addressed by the finite local carrier
index. -/
theorem finalCoordinatedSourceCarrierRoute_fallbackKind_eq_geometry
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
    (if (finalCoordinatedSourceRoutes retained
          clauseIndex literalIndex).dropLast.length = 1 then
        RetainedFallbackFanKind.escaped
      else RetainedFallbackFanKind.ordinary) =
      CarrierFallbackRouteTailRecords.routeKind
        (finalCarrierLocalClauseIndex taggedLink) literalIndex := by
  dsimp only
  have kindEq := finalCoordinatedSourceCarrierRoute_fallbackKind_eq
    source sourceLocal sourceWidth sourceClausesNonempty positiveOffsets
    taggedLink clauseIndex taggedLinkIndexed literalIndex
  dsimp only at kindEq
  simpa only [finalCarrierLocalClauseIndex_val] using kindEq

end PeriodicEightOccurrenceSplit
end LeanTrominoes
