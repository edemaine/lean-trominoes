/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedReindexingInjectivity
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedRoutePointReindexedRepresentatives

/-!
# Route-point occurrence identity under retained source reindexing

The first-segment witness of a route point lets the segment reindexing
injectivity theorem recover its original route and external shift.  Retaining
the point index then proves that translated metadata cannot collapse two
distinct periodic route-point occurrences.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- Transport a route-point representative across equality of its phantom
common-shift parameter. -/
private def castRoutePointCommonShiftRepresentative
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {indexed : IndexedRoutePoint}
    {shift sourceCommonShift targetCommonShift : Cell}
    (equal : sourceCommonShift = targetCommonShift)
    (representative :
      FinalGaugedRoutePointCommonShiftRepresentative
        formula indexed shift sourceCommonShift) :
    FinalGaugedRoutePointCommonShiftRepresentative
      formula indexed shift targetCommonShift :=
  equal ▸ representative

@[simp]
private theorem
    castRoutePointCommonShiftRepresentative_physicalIncidenceIndex
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {indexed : IndexedRoutePoint}
    {shift sourceCommonShift targetCommonShift : Cell}
    (equal : sourceCommonShift = targetCommonShift)
    (representative :
      FinalGaugedRoutePointCommonShiftRepresentative
        formula indexed shift sourceCommonShift) :
    (castRoutePointCommonShiftRepresentative
        equal representative).physicalIncidenceIndex =
      representative.physicalIncidenceIndex := by
  cases equal
  rfl

/-- Equal target finite incidences and point indices after source
reindexing imply equality of the original periodic route-point keys. -/
theorem
    FinalGaugedSegmentMetadataReindexing.routePointOccurrenceKey_eq_of_targetPhysicalIncidence_eq
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {firstIndexed secondIndexed : IndexedRoutePoint}
    {firstShift secondShift reindexShift : Cell}
    {first :
      FinalGaugedRoutePointOccurrenceWitness
        formula firstIndexed firstShift}
    (reindexing :
      FinalGaugedSegmentMetadataReindexing
        first.segmentWitness reindexShift)
    (second :
      FinalGaugedRoutePointOccurrenceWitness
        formula secondIndexed secondShift)
    (reindexShiftEq :
      reindexShift =
        Cell.sub first.segmentWitness.physicalShift
          second.segmentWitness.physicalShift)
    (sourceClauseNonempty :
      first.segmentWitness.routeWitness.metadata.clause.literals ≠ [])
    (targetPhysicalIncidenceEq :
      metadataPhysicalIncidence
          reindexing.targetMetadata
          reindexing.targetMetadataIndex
          reindexing.targetLiteral
          first.segmentWitness.taggedLiteral.2 =
        metadataPhysicalIncidence
          second.segmentWitness.routeWitness.metadata
          second.segmentWitness.routeWitness.metadataIndex
          second.segmentWitness.routeWitness.literal
          second.segmentWitness.taggedLiteral.2)
    (pointIndexEq :
      firstIndexed.pointIndex = secondIndexed.pointIndex) :
    PeriodicGridDrawing.RoutePointOccurrenceKey
        firstIndexed firstShift =
      PeriodicGridDrawing.RoutePointOccurrenceKey
        secondIndexed secondShift := by
  have segmentKeyEq :=
    reindexing.segmentOccurrenceKey_eq_of_targetPhysicalIncidence_eq
      second.segmentWitness reindexShiftEq sourceClauseNonempty
      targetPhysicalIncidenceEq rfl
  have routeIndexEq :
      firstIndexed.routeIndex = secondIndexed.routeIndex :=
    congrArg (fun key : Nat × Nat × Cell => key.1) segmentKeyEq
  have shiftEq : firstShift = secondShift :=
    congrArg (fun key : Nat × Nat × Cell => key.2.2) segmentKeyEq
  simp only [PeriodicGridDrawing.RoutePointOccurrenceKey,
    Prod.mk.injEq]
  exact ⟨routeIndexEq, pointIndexEq, shiftEq⟩

/-- Distinct original periodic route-point occurrences remain distinct as
finite incidence/point indices after reindexing the first source to the
second occurrence's physical shift. -/
theorem
    FinalGaugedSegmentMetadataReindexing.finitePointDifferent_of_routePointOccurrenceKey_ne
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {firstIndexed secondIndexed : IndexedRoutePoint}
    {firstShift secondShift : Cell}
    {first :
      FinalGaugedRoutePointOccurrenceWitness
        formula firstIndexed firstShift}
    (second :
      FinalGaugedRoutePointOccurrenceWitness
        formula secondIndexed secondShift)
    (reindexing :
      FinalGaugedSegmentMetadataReindexing first.segmentWitness
        (Cell.sub first.segmentWitness.physicalShift
          second.segmentWitness.physicalShift))
    (sourceClauseNonempty :
      first.segmentWitness.routeWitness.metadata.clause.literals ≠ [])
    (different :
      PeriodicGridDrawing.RoutePointOccurrenceKey
          firstIndexed firstShift ≠
        PeriodicGridDrawing.RoutePointOccurrenceKey
          secondIndexed secondShift) :
    (reindexing.toRoutePointCommonShiftRepresentative).physicalIncidenceIndex ≠
          second.segmentWitness.physicalIncidenceIndex ∨
      firstIndexed.pointIndex ≠ secondIndexed.pointIndex := by
  by_cases incidenceIndexNe :
      reindexing.targetPhysicalIncidenceIndex ≠
        second.segmentWitness.physicalIncidenceIndex
  · left
    simpa only [
      FinalGaugedSegmentMetadataReindexing.toRoutePointCommonShiftRepresentative_physicalIncidenceIndex]
      using incidenceIndexNe
  · right
    intro pointIndexEq
    apply different
    have incidenceIndexEq :
        reindexing.targetPhysicalIncidenceIndex =
          second.segmentWitness.physicalIncidenceIndex :=
      not_ne_iff.mp incidenceIndexNe
    have targetLookup :=
      (List.mem_zipIdx_iff_getElem?).mp
        reindexing.targetPhysicalIncidenceMember
    have secondLookup :=
      (List.mem_zipIdx_iff_getElem?).mp
        second.segmentWitness.physicalIncidenceMember
    rw [incidenceIndexEq] at targetLookup
    have targetPhysicalIncidenceEq :
        metadataPhysicalIncidence
            reindexing.targetMetadata
            reindexing.targetMetadataIndex
            reindexing.targetLiteral
            first.segmentWitness.taggedLiteral.2 =
          metadataPhysicalIncidence
            second.segmentWitness.routeWitness.metadata
            second.segmentWitness.routeWitness.metadataIndex
            second.segmentWitness.routeWitness.literal
            second.segmentWitness.taggedLiteral.2 :=
      Option.some.inj
        (targetLookup.symm.trans secondLookup)
    exact
      reindexing.routePointOccurrenceKey_eq_of_targetPhysicalIncidence_eq
        second rfl sourceClauseNonempty
        targetPhysicalIncidenceEq pointIndexEq

/-- Reindexing a distinct first point occurrence to the second occurrence's
physical shift transfers finite endpoint-only contact to the original pair. -/
theorem
    FinalGaugedSegmentMetadataReindexing.routePointsAreEndpoints
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      formula.incidenceGraph.IsWellFormed)
    (degree :
      formula.incidenceGraph.DegreeAtMost 3)
    (isLocal :
      formula.incidenceGraph.IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ [])
    {firstIndexed secondIndexed : IndexedRoutePoint}
    {firstShift secondShift : Cell}
    {first :
      FinalGaugedRoutePointOccurrenceWitness
        formula firstIndexed firstShift}
    (second :
      FinalGaugedRoutePointOccurrenceWitness
        formula secondIndexed secondShift)
    (reindexing :
      FinalGaugedSegmentMetadataReindexing first.segmentWitness
        (Cell.sub first.segmentWitness.physicalShift
          second.segmentWitness.physicalShift))
    (sourceClauseNonempty :
      first.segmentWitness.routeWitness.metadata.clause.literals ≠ [])
    (different :
      PeriodicGridDrawing.RoutePointOccurrenceKey
          firstIndexed firstShift ≠
        PeriodicGridDrawing.RoutePointOccurrenceKey
          secondIndexed secondShift)
    (equal :
      Cell.add firstIndexed.point
          ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).periodTranslation firstShift) =
        Cell.add secondIndexed.point
          ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).periodTranslation secondShift)) :
    firstIndexed.IsEndpoint ∧ secondIndexed.IsEndpoint := by
  have commonShiftEq :
      Cell.sub first.segmentWitness.physicalShift
          (Cell.sub first.segmentWitness.physicalShift
            second.segmentWitness.physicalShift) =
        second.segmentWitness.physicalShift := by
    rcases first.segmentWitness.physicalShift with ⟨firstX, firstY⟩
    rcases second.segmentWitness.physicalShift with ⟨secondX, secondY⟩
    simp [Cell.sub]
  let firstRepresentative :=
    castRoutePointCommonShiftRepresentative commonShiftEq
      reindexing.toRoutePointCommonShiftRepresentative
  exact
    retainedDeduplicatedGaugedWrappedDrawing_commonShiftRepresentatives_routePointsAreEndpoints
      formula wellFormed degree isLocal clausesNonempty
      firstRepresentative second.toCommonShiftRepresentative
      (by
        simpa only [firstRepresentative,
          castRoutePointCommonShiftRepresentative_physicalIncidenceIndex,
          FinalGaugedRoutePointOccurrenceWitness.toCommonShiftRepresentative]
          using
            finitePointDifferent_of_routePointOccurrenceKey_ne
              second reindexing sourceClauseNonempty different)
      equal

/-- A retained source-orbit condition is sufficient to transfer finite
endpoint-only contact to distinct final periodic route-point occurrences. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_routePointsAreEndpoints_of_first_retainedOrbitCondition
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      formula.incidenceGraph.IsWellFormed)
    (degree :
      formula.incidenceGraph.DegreeAtMost 3)
    (isLocal :
      formula.incidenceGraph.IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ [])
    {firstIndexed secondIndexed : IndexedRoutePoint}
    {firstShift secondShift : Cell}
    (first :
      FinalGaugedRoutePointOccurrenceWitness
        formula firstIndexed firstShift)
    (second :
      FinalGaugedRoutePointOccurrenceWitness
        formula secondIndexed secondShift)
    (condition :
      first.segmentWitness.routeWitness.metadata.source.RetainedOrbitCondition
          formula
          (Cell.sub first.segmentWitness.physicalShift
            second.segmentWitness.physicalShift))
    (different :
      PeriodicGridDrawing.RoutePointOccurrenceKey
          firstIndexed firstShift ≠
        PeriodicGridDrawing.RoutePointOccurrenceKey
          secondIndexed secondShift)
    (equal :
      Cell.add firstIndexed.point
          ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).periodTranslation firstShift) =
        Cell.add secondIndexed.point
          ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).periodTranslation secondShift)) :
    firstIndexed.IsEndpoint ∧ secondIndexed.IsEndpoint := by
  let firstSegment := first.segmentWitness
  let secondSegment := second.segmentWitness
  rcases
      firstSegment.routeWitness.metadata.source
        |>.exists_retainedTarget_periodTranslate
          formula degree firstSegment.source_retainedComponentMember
          (Cell.sub firstSegment.physicalShift
            secondSegment.physicalShift)
          condition with
    ⟨targetSource, targetMember,
      targetComponentEq, targetLocalClauseIndexEq⟩
  rcases firstSegment.exists_metadataReindexing_of_targetSource
      targetSource targetMember targetComponentEq
      targetLocalClauseIndexEq with
    ⟨reindexing⟩
  have sourceMetadataMember :
      firstSegment.routeWitness.metadata ∈
        retainedDrawingPlanarSATClauseMetadata formula :=
    List.mem_iff_getElem?.mpr
      ⟨firstSegment.routeWitness.metadataIndex,
        firstSegment.routeWitness.metadataLookup⟩
  have sourceClauseMember :
      firstSegment.routeWitness.metadata.clause ∈
        retainedDrawingPlanarSATFormula formula := by
    rw [← retainedDrawingPlanarSATClauseMetadata_clauses]
    exact List.mem_map.mpr
      ⟨firstSegment.routeWitness.metadata,
        sourceMetadataMember, rfl⟩
  exact
    FinalGaugedSegmentMetadataReindexing.routePointsAreEndpoints
      formula wellFormed degree isLocal clausesNonempty
      second reindexing
      (clausesNonempty
        firstSegment.routeWitness.metadata.clause sourceClauseMember)
      different equal

end PeriodicOrthocrossing
end LeanTrominoes
