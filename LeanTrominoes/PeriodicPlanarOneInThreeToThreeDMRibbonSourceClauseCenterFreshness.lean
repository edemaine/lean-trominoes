/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceClauseCoreCorridorSeparation
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceClauseFanOrder
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceClauseRouteOrder

/-!
# Clause centers are fresh along source-route interiors

In the zero-anchor gauge, literal zero of every nonempty source clause has
offset zero.  Its active occurrence route therefore ends at the canonical
clause center.  Endpoint-only contacts between unit-subdivided source routes
then force any other occurrence route that lists this center to list it only
as an outer endpoint, never among the interior macrocell centers used by its
ribbon corridor.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM PeriodicOrthocrossing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- In a duplicate-free route, a point in the tail with the final point
removed cannot be an outer route endpoint. -/
theorem not_routePointIsEndpoint_of_mem_tail_dropLast_of_nodup
    {route : List Cell} {point : Cell}
    (nodup : route.Nodup)
    (member : point ∈ route.tail.dropLast) :
    ¬RoutePointIsEndpoint route point := by
  intro endpoint
  have routeLength : 2 ≤ route.length := by
    cases route with
    | nil => simp at member
    | cons first rest =>
        cases rest with
        | nil => simp at member
        | cons second rest => simp
  cases routeEquation : route with
  | nil => simp [routeEquation] at routeLength
  | cons first rest =>
      cases rest with
      | nil => simp [routeEquation] at routeLength
      | cons second rest =>
          have routeNodup : (first :: second :: rest).Nodup := by
            simpa [routeEquation] using nodup
          have tailMember : point ∈ second :: rest :=
            List.mem_of_mem_dropLast (by simpa [routeEquation] using member)
          have headNe : point ≠ first := by
            have fresh := (List.nodup_cons.mp routeNodup).1
            exact fun equal => fresh (equal ▸ tailMember)
          have dropLastMember :
              point ∈ (first :: second :: rest).dropLast := by
            rw [List.dropLast_cons_of_ne_nil (by simp)]
            exact List.mem_cons_of_mem first
              (by simpa [routeEquation] using member)
          rcases endpoint with head | last
          · rw [routeEquation] at head
            simp only [List.head?_cons, Option.some.injEq] at head
            exact headNe head.symm
          · have lastNe :=
              getLast?_ne_some_of_mem_dropLast_of_nodup
                routeNodup dropLastMember
            rw [routeEquation] at last
            exact lastNe last

/-- Literal zero of a declared arity-two-or-three clause supplies an active
unit source route ending at that clause's canonical center. -/
theorem exists_occurrenceUnitSourceRoute_ending_at_clauseCenter
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (anchorsZero : HasZeroClauseAnchors source)
    (occurrences : source.erase.OccurrencesAtMost 3)
    (arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree source.erase)
    (clauseIndex : Nat)
    (indexLt : clauseIndex < source.clauses.length) :
    ∃ entry : ActiveOccurrenceEntry source.erase,
      (occurrenceUnitSourceRoute presentation entry).getLast? =
        some (positionedClausePositionAt source clauseIndex) := by
  let positionedClause := source.clauses[clauseIndex]
  have clauseMember :
      (positionedClause, clauseIndex) ∈ source.clauses.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?, List.getElem?_eq_some_iff]
    exact ⟨indexLt, rfl⟩
  have erasedClauseMember :
      positionedClause.literals ∈ source.erase.clauses := by
    change positionedClause.literals ∈
      source.clauses.map PositionedPeriodicClause.literals
    exact List.mem_map.mpr
      ⟨positionedClause, List.fst_mem_of_mem_zipIdx clauseMember, rfl⟩
  have clauseArity :=
    arity positionedClause.literals erasedClauseMember
  have zeroLt : 0 < positionedClause.literals.length := by
    rcases clauseArity with two | three <;> omega
  rcases exists_activeClauseOccurrenceEntry_of_literalIndex
      occurrences clauseMember zeroLt with
    ⟨entry, entryClauseMember, entryLiteralIndex⟩
  let data := occurrenceSpliceData presentation entry
  have dataClauseIndex : data.indexed.1.clauseIndex = clauseIndex := by
    rw [← occurrenceClauseIndex_eq_indexedClauseIndex
      presentation entry]
    exact (mem_activeClauseOccurrenceEntries_iff
      source.erase clauseIndex entry).mp entryClauseMember
  have dataLiteralIndex : data.indexed.1.literalIndex = 0 := by
    rw [← occurrenceLiteralIndex_eq_indexedLiteralIndex
      presentation entry]
    exact entryLiteralIndex
  have dataClauseMember :
      (data.positionedClause, clauseIndex) ∈ source.clauses.zipIdx := by
    simpa [dataClauseIndex] using data.clauseMember
  have positionedClauseEq : data.positionedClause = positionedClause :=
    (List.mem_zipIdx' dataClauseMember).2.trans
      (List.mem_zipIdx' clauseMember).2.symm
  have indexedClauseEq :
      data.indexed.1.clause = positionedClause.literals := by
    rw [← positionedClauseEq]
    exact indexedIncidence_clause_eq_positionedClause_literals
      data.indexedMember data.clauseMember
  have indexedIncidenceMember :
      data.indexed.1 ∈
        PeriodicCNF.incidencesWithMetadata source.erase :=
    List.fst_mem_of_mem_zipIdx data.indexedMember
  have indexedLiteralMember :
      (data.indexed.1.literal, data.indexed.1.literalIndex) ∈
        data.indexed.1.clause.zipIdx :=
    (PeriodicCNF.mem_incidencesWithMetadata_iff
      source.erase data.indexed.1).mp indexedIncidenceMember |>.2
  have headEq :
      positionedClause.literals.head? =
        some data.indexed.1.literal := by
    rw [indexedClauseEq, dataLiteralIndex] at indexedLiteralMember
    have lookup :=
      (List.mem_zipIdx_iff_getElem?).mp indexedLiteralMember
    simpa only [List.head?_eq_getElem?] using lookup
  have indexedLiteralOffsetZero :
      data.indexed.1.literal.offset = (0, 0) := by
    have anchorZero := anchorsZero positionedClause
      (List.fst_mem_of_mem_zipIdx clauseMember)
    simp only [PeriodicCNF.clauseAnchor, headEq,
      Option.map_some, Option.getD_some] at anchorZero
    exact anchorZero
  have indexedLiteralEq :
      data.indexed.1.literal = data.tagged.1 :=
    congrArg Prod.fst data.metadataEq
  have taggedOffsetZero : data.tagged.1.offset = (0, 0) := by
    rw [← indexedLiteralEq]
    exact indexedLiteralOffsetZero
  have targetEq :
      occurrenceSourceClauseTarget presentation entry =
        positionedClausePositionAt source clauseIndex := by
    simp [occurrenceSourceClauseTarget, data, positionedClauseEq,
      taggedOffsetZero, PositionedPeriodicCNF.variableToClauseTarget,
      PeriodicOneInThreeToThreeDM.reverseOffset,
      PeriodicVariablePlacement.translation,
      positionedClausePositionAt, positionedClause,
      List.getElem?_eq_getElem indexLt, Cell.add, Cell.scale]
  refine ⟨entry, ?_⟩
  exact (occurrenceUnitSourceRoute_endpoints
    presentation entry).2.trans (congrArg some targetEq)

/-- No unit-subdivided source route uses a canonical clause center as one of
the interior macrocell centers that generate its ribbon corridor. -/
theorem clauseCenter_not_mem_occurrenceUnitSourceRoute_tail_dropLast
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (anchorsZero : HasZeroClauseAnchors source)
    (occurrences : source.erase.OccurrencesAtMost 3)
    (arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree source.erase)
    (clauseIndex : Nat)
    (indexLt : clauseIndex < source.clauses.length)
    (entry : ActiveOccurrenceEntry source.erase) :
    positionedClausePositionAt source clauseIndex ∉
      (occurrenceUnitSourceRoute
        presentation.toPlanarIncidencePresentation entry).tail.dropLast := by
  let planar := presentation.toPlanarIncidencePresentation
  let route := occurrenceUnitSourceRoute planar entry
  intro centerMember
  have routeNodup : route.Nodup := by
    simpa [route, planar] using
      occurrenceUnitSourceRoute_nodup presentation entry
  have notEndpoint :
      ¬RoutePointIsEndpoint route
        (positionedClausePositionAt source clauseIndex) :=
    not_routePointIsEndpoint_of_mem_tail_dropLast_of_nodup
      routeNodup (by simpa [route, planar] using centerMember)
  rcases exists_occurrenceUnitSourceRoute_ending_at_clauseCenter
      planar anchorsZero occurrences arity clauseIndex indexLt with
    ⟨covering, coveringLast⟩
  by_cases same : entry = covering
  · subst covering
    exact notEndpoint (Or.inr (by simpa [route, planar] using coveringLast))
  · have meetOnly :=
      occurrenceUnitSourceRoutes_meetOnlyAtEndpoints_of_ne
        presentation same
    have routeMember :
        positionedClausePositionAt source clauseIndex ∈ route := by
      apply List.mem_of_mem_tail
      exact List.mem_of_mem_dropLast
        (by simpa [route, planar] using centerMember)
    have coveringMember :
        positionedClausePositionAt source clauseIndex ∈
          occurrenceUnitSourceRoute planar covering :=
      mem_of_getLast?_eq_some coveringLast
    rcases List.mem_iff_get.mp routeMember with
      ⟨routeIndex, routePointEq⟩
    rcases List.mem_iff_get.mp coveringMember with
      ⟨coveringIndex, coveringPointEq⟩
    have endpoints := meetOnly routeIndex coveringIndex
      (routePointEq.trans coveringPointEq.symm)
    apply notEndpoint
    have endpointAtIndex :
        RoutePointIsEndpoint route (route.get routeIndex) := by
      simpa [route, planar] using endpoints.1
    rw [routePointEq] at endpointAtIndex
    exact endpointAtIndex

/-- Under the source arity and occurrence bounds, the checked clause core
strictly avoids every occurrence corridor; freshness is now discharged from
the global source-route endpoint invariant. -/
theorem constructedClauseRoute_strictlyAvoids_occurrenceRibbonCorridorCore
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (anchorsZero : HasZeroClauseAnchors source)
    (occurrences : source.erase.OccurrencesAtMost 3)
    (arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree source.erase)
    (clauseIndex : Nat)
    (indexLt : clauseIndex < source.clauses.length)
    (set : X3CClauseSet)
    (coreColor : WireColor)
    (entry : ActiveOccurrenceEntry source.erase)
    (corridorColor : WireColor) :
    RoutesStrictlyAvoidEachOther
      (translatePolyline
        (constructedClauseOrigin source standardThreeStrandLayout
          clauseIndex)
        (X3CClauseOrthogonal.route set coreColor))
      (occurrenceRibbonCorridorCore
        presentation.toPlanarIncidencePresentation entry corridorColor) :=
  constructedClauseRoute_strictlyAvoids_occurrenceRibbonCorridorCore_of_interior_fresh
    presentation anchorsZero clauseIndex indexLt set coreColor entry
    corridorColor
    (clauseCenter_not_mem_occurrenceUnitSourceRoute_tail_dropLast
      presentation anchorsZero occurrences arity clauseIndex indexLt entry)

/-- The corresponding assembled clause core strictly avoids every occurrence
corridor in the coordinated routing. -/
theorem assembledClauseRoute_strictlyAvoids_occurrenceRibbonCorridorCore
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (anchorsZero : HasZeroClauseAnchors source)
    (occurrences : source.erase.OccurrencesAtMost 3)
    (arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree source.erase)
    (width : source.erase.WidthAtMost 3)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (clauseIndex : Nat)
    (indexLt : clauseIndex < source.clauses.length)
    (set : X3CClauseSet)
    (coreColor : WireColor)
    (entry : ActiveOccurrenceEntry source.erase)
    (corridorColor : WireColor) :
    let routing := coordinatedSourceRibbonThreeStrandRouting
      presentation width compatible
    RoutesStrictlyAvoidEachOther
      (assembledClauseRoute routing clauseIndex set coreColor)
      (occurrenceRibbonCorridorCore
        presentation.toPlanarIncidencePresentation entry corridorColor) := by
  apply
    assembledClauseRoute_strictlyAvoids_occurrenceRibbonCorridorCore_of_interior_fresh
      presentation anchorsZero width compatible clauseIndex indexLt set
      coreColor entry corridorColor
  exact clauseCenter_not_mem_occurrenceUnitSourceRoute_tail_dropLast
    presentation anchorsZero occurrences arity clauseIndex indexLt entry

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
