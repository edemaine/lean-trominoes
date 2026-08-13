/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.EmbeddedCNFIncidenceDrawingIndexedRoutePointSeparation
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATFinitePlanarity
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedRoutePointOccurrences

/-!
# Common-shift retained route-point representatives

Finite endpoint-contact separation applies once two final periodic route
points have genuine representatives in one common translate of the retained
finite drawing.  This file records exactly that interface and transfers the
finite drawing's route simplicity and endpoint-only contact certificate.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 1200000

/-- A final periodic route-point occurrence represented by a same-indexed
point of one genuine retained route at a prescribed common lattice shift. -/
structure FinalGaugedRoutePointCommonShiftRepresentative
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (indexed : IndexedRoutePoint)
    (shift commonShift : Cell) where
  physicalIncidence :
    EmbeddedCNFIncidence (PlanarSATVariable Variable)
  physicalIncidenceIndex : Nat
  physicalIncidenceMember :
    (physicalIncidence, physicalIncidenceIndex) ∈
      (retainedDrawingPlanarSATLocalIncidenceDrawing
        formula).incidences.zipIdx
  physicalPoint : Cell
  physicalPointMember :
    (physicalPoint, indexed.pointIndex) ∈
      ((retainedDrawingPlanarSATLocalIncidenceDrawing formula).routeAt
        physicalIncidence).zipIdx
  physicalRouteLengthEq :
    ((retainedDrawingPlanarSATLocalIncidenceDrawing formula).routeAt
      physicalIncidence).length =
        indexed.routeLength
  pointEq :
    Cell.add indexed.point
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation shift) =
      Cell.add physicalPoint
        ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
          formula).translation commonShift)

/-- The original quotient-to-finite point witness is a common-shift
representative at its anchor-adjusted physical shift. -/
def FinalGaugedRoutePointOccurrenceWitness.toCommonShiftRepresentative
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {indexed : IndexedRoutePoint}
    {shift : Cell}
    (witness :
      FinalGaugedRoutePointOccurrenceWitness formula indexed shift) :
    FinalGaugedRoutePointCommonShiftRepresentative
      formula indexed shift witness.segmentWitness.physicalShift where
  physicalIncidence :=
    metadataPhysicalIncidence
      witness.segmentWitness.routeWitness.metadata
      witness.segmentWitness.routeWitness.metadataIndex
      witness.segmentWitness.routeWitness.literal
      witness.segmentWitness.taggedLiteral.2
  physicalIncidenceIndex :=
    witness.segmentWitness.physicalIncidenceIndex
  physicalIncidenceMember :=
    witness.segmentWitness.physicalIncidenceMember
  physicalPoint := witness.physicalPoint
  physicalPointMember := witness.physicalPointMember
  physicalRouteLengthEq := witness.physicalRouteLengthEq
  pointEq := witness.pointEq

/-- The finite indexed point carried by a common-shift representative. -/
def FinalGaugedRoutePointCommonShiftRepresentative.physicalIndexedPoint
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {indexed : IndexedRoutePoint}
    {shift commonShift : Cell}
    (representative :
      FinalGaugedRoutePointCommonShiftRepresentative
        formula indexed shift commonShift) :
    IndexedRoutePoint where
  routeIndex := representative.physicalIncidenceIndex
  pointIndex := indexed.pointIndex
  routeLength :=
    ((retainedDrawingPlanarSATLocalIncidenceDrawing formula).routeAt
      representative.physicalIncidence).length
  point := representative.physicalPoint

/-- A common-shift representative preserves outer endpoint status. -/
theorem
    FinalGaugedRoutePointCommonShiftRepresentative.physicalIndexedPoint_isEndpoint_iff
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {indexed : IndexedRoutePoint}
    {shift commonShift : Cell}
    (representative :
      FinalGaugedRoutePointCommonShiftRepresentative
        formula indexed shift commonShift) :
    representative.physicalIndexedPoint.IsEndpoint ↔
      indexed.IsEndpoint := by
  simp only [IndexedRoutePoint.IsEndpoint,
    FinalGaugedRoutePointCommonShiftRepresentative.physicalIndexedPoint]
  rw [representative.physicalRouteLengthEq]

/-- Two distinct indexed finite point occurrences represented at one common
shift can coincide only as outer endpoints of both routes. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_commonShiftRepresentatives_routePointsAreEndpoints
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ [])
    {firstIndexed secondIndexed : IndexedRoutePoint}
    {firstShift secondShift commonShift : Cell}
    (first :
      FinalGaugedRoutePointCommonShiftRepresentative
        formula firstIndexed firstShift commonShift)
    (second :
      FinalGaugedRoutePointCommonShiftRepresentative
        formula secondIndexed secondShift commonShift)
    (finiteDifferent :
      first.physicalIncidenceIndex ≠
          second.physicalIncidenceIndex ∨
        firstIndexed.pointIndex ≠ secondIndexed.pointIndex)
    (equal :
      Cell.add firstIndexed.point
          ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).periodTranslation firstShift) =
        Cell.add secondIndexed.point
          ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).periodTranslation secondShift)) :
    firstIndexed.IsEndpoint ∧ secondIndexed.IsEndpoint := by
  let finiteDrawing :=
    retainedDrawingPlanarSATLocalIncidenceDrawing formula
  let placement :=
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula
  have liftedPhysicalPointEq :
      Cell.add first.physicalPoint
          (placement.translation commonShift) =
        Cell.add second.physicalPoint
          (placement.translation commonShift) :=
    first.pointEq.symm.trans (equal.trans second.pointEq)
  have physicalPointEq :
      first.physicalPoint = second.physicalPoint := by
    apply
      Cell.add_left_injective
        (placement.translation commonShift)
    simpa [Cell.add, add_comm] using liftedPhysicalPointEq
  have finitePlanar :
      finiteDrawing.IsPlanar :=
    retainedDrawingPlanarSATLocalIncidenceDrawing_isPlanar
      formula wellFormed degree isLocal clausesNonempty
  by_cases incidenceIndexEq :
      first.physicalIncidenceIndex =
        second.physicalIncidenceIndex
  · have pointIndexNe :
        firstIndexed.pointIndex ≠ secondIndexed.pointIndex := by
      rcases finiteDifferent with incidenceIndexNe | pointIndexNe
      · exact False.elim (incidenceIndexNe incidenceIndexEq)
      · exact pointIndexNe
    have firstIncidenceLookup :=
      (List.mem_zipIdx_iff_getElem?).mp
        first.physicalIncidenceMember
    have secondIncidenceLookup :=
      (List.mem_zipIdx_iff_getElem?).mp
        second.physicalIncidenceMember
    have physicalIncidenceEq :
        first.physicalIncidence = second.physicalIncidence := by
      rw [incidenceIndexEq] at firstIncidenceLookup
      exact Option.some.inj
        (firstIncidenceLookup.symm.trans secondIncidenceLookup)
    have incidenceIndexLt :
        first.physicalIncidenceIndex <
          finiteDrawing.incidences.length :=
      List.snd_lt_of_mem_zipIdx first.physicalIncidenceMember
    let incidenceIndex : Fin finiteDrawing.incidences.length :=
      ⟨first.physicalIncidenceIndex, incidenceIndexLt⟩
    have incidenceAt :
        finiteDrawing.incidenceAt incidenceIndex =
          first.physicalIncidence := by
      exact
        (List.getElem?_eq_some_iff.mp firstIncidenceLookup).2
    have simple := finitePlanar.1 incidenceIndex
    change
      LocalIncidenceDrawing.RouteIsSimple
        (finiteDrawing.routeAt
          (finiteDrawing.incidenceAt incidenceIndex))
      at simple
    rw [incidenceAt] at simple
    have firstPointLookup :=
      (List.mem_zipIdx_iff_getElem?).mp first.physicalPointMember
    have secondPointLookup :=
      (List.mem_zipIdx_iff_getElem?).mp second.physicalPointMember
    have firstPointLookup' :
        (finiteDrawing.routeAt first.physicalIncidence)[
            firstIndexed.pointIndex]? =
          some second.physicalPoint :=
      firstPointLookup.trans (congrArg some physicalPointEq)
    have secondPointLookup' :
        (finiteDrawing.routeAt first.physicalIncidence)[
            secondIndexed.pointIndex]? =
          some second.physicalPoint := by
      simpa only [physicalIncidenceEq] using secondPointLookup
    exact False.elim
      (pointIndexNe
        (List.Nodup.index_eq_of_getElem?_eq_some
          simple.1 firstPointLookup' secondPointLookup'))
  · have firstIncidenceIndexLt :
        first.physicalIncidenceIndex <
          finiteDrawing.incidences.length :=
      List.snd_lt_of_mem_zipIdx first.physicalIncidenceMember
    have secondIncidenceIndexLt :
        second.physicalIncidenceIndex <
          finiteDrawing.incidences.length :=
      List.snd_lt_of_mem_zipIdx second.physicalIncidenceMember
    let firstIncidenceIndex : Fin finiteDrawing.incidences.length :=
      ⟨first.physicalIncidenceIndex, firstIncidenceIndexLt⟩
    let secondIncidenceIndex : Fin finiteDrawing.incidences.length :=
      ⟨second.physicalIncidenceIndex, secondIncidenceIndexLt⟩
    have firstIncidenceAt :
        finiteDrawing.incidenceAt firstIncidenceIndex =
          first.physicalIncidence := by
      exact
        (List.getElem?_eq_some_iff.mp
          ((List.mem_zipIdx_iff_getElem?).mp
            first.physicalIncidenceMember)).2
    have secondIncidenceAt :
        finiteDrawing.incidenceAt secondIncidenceIndex =
          second.physicalIncidence := by
      exact
        (List.getElem?_eq_some_iff.mp
          ((List.mem_zipIdx_iff_getElem?).mp
            second.physicalIncidenceMember)).2
    have finiteIncidenceIndexNe :
        firstIncidenceIndex ≠ secondIncidenceIndex := by
      intro indexEq
      exact incidenceIndexEq (congrArg Fin.val indexEq)
    have separated :=
      finitePlanar.2.1
        firstIncidenceIndex secondIncidenceIndex
        finiteIncidenceIndexNe
    change
      EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
        (finiteDrawing.routeAt
          (finiteDrawing.incidenceAt firstIncidenceIndex))
        (finiteDrawing.routeAt
          (finiteDrawing.incidenceAt secondIncidenceIndex))
      at separated
    rw [firstIncidenceAt, secondIncidenceAt] at separated
    have firstPointIndexLt :
        firstIndexed.pointIndex <
          (finiteDrawing.routeAt first.physicalIncidence).length :=
      List.snd_lt_of_mem_zipIdx first.physicalPointMember
    have secondPointIndexLt :
        secondIndexed.pointIndex <
          (finiteDrawing.routeAt second.physicalIncidence).length :=
      List.snd_lt_of_mem_zipIdx second.physicalPointMember
    let firstPointIndex :
        Fin (finiteDrawing.routeAt first.physicalIncidence).length :=
      ⟨firstIndexed.pointIndex, firstPointIndexLt⟩
    let secondPointIndex :
        Fin (finiteDrawing.routeAt second.physicalIncidence).length :=
      ⟨secondIndexed.pointIndex, secondPointIndexLt⟩
    have firstPointAt :
        (finiteDrawing.routeAt first.physicalIncidence).get
            firstPointIndex =
          first.physicalPoint :=
      (List.getElem?_eq_some_iff.mp
        ((List.mem_zipIdx_iff_getElem?).mp
          first.physicalPointMember)).2
    have secondPointAt :
        (finiteDrawing.routeAt second.physicalIncidence).get
            secondPointIndex =
          second.physicalPoint :=
      (List.getElem?_eq_some_iff.mp
        ((List.mem_zipIdx_iff_getElem?).mp
          second.physicalPointMember)).2
    have physicalEndpoints :=
      separated.2.2.2 firstPointIndex secondPointIndex
        (by simpa only [firstPointAt, secondPointAt] using physicalPointEq)
    have physicalEndpoints' :
        EmbeddedCNFIncidenceDrawing.RoutePointIsEndpoint
            (finiteDrawing.routeAt first.physicalIncidence)
            first.physicalPoint ∧
          EmbeddedCNFIncidenceDrawing.RoutePointIsEndpoint
            (finiteDrawing.routeAt second.physicalIncidence)
            second.physicalPoint := by
      simpa only [firstPointAt, secondPointAt] using physicalEndpoints
    have firstSimple := finitePlanar.1 firstIncidenceIndex
    change
      LocalIncidenceDrawing.RouteIsSimple
        (finiteDrawing.routeAt
          (finiteDrawing.incidenceAt firstIncidenceIndex))
      at firstSimple
    rw [firstIncidenceAt] at firstSimple
    have secondSimple := finitePlanar.1 secondIncidenceIndex
    change
      LocalIncidenceDrawing.RouteIsSimple
        (finiteDrawing.routeAt
          (finiteDrawing.incidenceAt secondIncidenceIndex))
      at secondSimple
    rw [secondIncidenceAt] at secondSimple
    have firstPhysicalEndpoint :
        first.physicalIndexedPoint.IsEndpoint := by
      have indexedEndpoint :=
        EmbeddedCNFIncidenceDrawing.indexedRoutePoint_isEndpoint_of_routePointIsEndpoint
          firstSimple.1 first.physicalPointMember physicalEndpoints'.1
      simpa only [
        FinalGaugedRoutePointCommonShiftRepresentative.physicalIndexedPoint,
        IndexedRoutePoint.IsEndpoint] using indexedEndpoint
    have secondPhysicalEndpoint :
        second.physicalIndexedPoint.IsEndpoint := by
      have indexedEndpoint :=
        EmbeddedCNFIncidenceDrawing.indexedRoutePoint_isEndpoint_of_routePointIsEndpoint
          secondSimple.1 second.physicalPointMember physicalEndpoints'.2
      simpa only [
        FinalGaugedRoutePointCommonShiftRepresentative.physicalIndexedPoint,
        IndexedRoutePoint.IsEndpoint] using indexedEndpoint
    exact
      ⟨(first.physicalIndexedPoint_isEndpoint_iff).mp
          firstPhysicalEndpoint,
        (second.physicalIndexedPoint_isEndpoint_iff).mp
          secondPhysicalEndpoint⟩

end PeriodicOrthocrossing
end LeanTrominoes
