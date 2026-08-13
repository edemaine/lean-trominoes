/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.EmbeddedCNFIncidenceDrawingIndexedRoutePointSeparation
import LeanTrominoes.PeriodicGridDrawingRouteOccurrenceSeparation
import LeanTrominoes.PeriodicGridDrawingUnitSubdivision

/-!
# Reassembling global periodic separation from lifted routes

The ribbon construction often establishes geometry one pair of complete
lifted routes at a time.  The periodic drawing interface instead quantifies
over globally indexed segment and point occurrences.  This module records
the converse bridge for listed-point contacts: complete avoidance of every
pair of distinct lifted route occurrences, together with simplicity of each
stored route, implies the drawing-level endpoint-contact predicate.
-/

namespace LeanTrominoes
namespace PeriodicGridDrawing

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Every pair of distinct complete route occurrences in the periodic lift
satisfies the finite ribbon-separation predicate. -/
def LiftedRoutesAvoidEachOther (drawing : PeriodicGridDrawing) : Prop :=
  ∀ first ∈ drawing.edgeRoutes.zipIdx,
    ∀ second ∈ drawing.edgeRoutes.zipIdx,
      ∀ firstTranslate secondTranslate,
        (first.2, firstTranslate) ≠
            (second.2, secondTranslate) →
          RoutesAvoidEachOther
            (first.1.map
              (Cell.add
                (drawing.periodTranslation firstTranslate)))
            (second.1.map
              (Cell.add
                (drawing.periodTranslation secondTranslate)))

/-- Translation-invariant form of `LiftedRoutesAvoidEachOther`: hold the
first route in the fundamental representative and translate only the second
route by the relative lattice shift.  This is the convenient interface for
geometric constructions whose local separation theorem is stated relative
to one source block. -/
def RelativeLiftedRoutesAvoidEachOther
    (drawing : PeriodicGridDrawing) : Prop :=
  ∀ first ∈ drawing.edgeRoutes.zipIdx,
    ∀ second ∈ drawing.edgeRoutes.zipIdx,
      ∀ relativeTranslate,
        (first.2, (0, 0)) ≠
            (second.2, relativeTranslate) →
          RoutesAvoidEachOther
            first.1
            (second.1.map
              (Cell.add
                (drawing.periodTranslation relativeTranslate)))

/-- Ribbon readiness is also sufficient for relative complete route
separation when every stored route is nondegenerate and made of unit lattice
steps.  Unit steps supply both directed point/interior conditions, while the
ribbon fields supply continuous segment separation and endpoint-only listed
contacts. -/
theorem relativeLiftedRoutesAvoidEachOther_of_isRibbonReady_of_hasUnitSteps
    {drawing : PeriodicGridDrawing}
    (ribbonReady : drawing.IsRibbonReady)
    (unitSteps : drawing.HasUnitSteps)
    (lengths :
      ∀ route ∈ drawing.edgeRoutes,
        2 ≤ route.length) :
    drawing.RelativeLiftedRoutesAvoidEachOther := by
  intro first firstMember second secondMember
    relativeTranslate occurrencesDifferent
  have avoids :=
    routeOccurrences_avoidEachOther_of_segmentEndpointsAvoid
      ribbonReady.1
      (segmentEndpointsAvoidInteriors_of_hasUnitSteps unitSteps)
      ribbonReady.2
      firstMember secondMember
      (lengths first.1 (List.fst_mem_of_mem_zipIdx firstMember))
      (lengths second.1 (List.fst_mem_of_mem_zipIdx secondMember))
      (0, 0) relativeTranslate occurrencesDifferent
  have zeroTranslate :
      first.1.map
          (Cell.add (drawing.periodTranslation (0, 0))) =
        first.1 := by
    induction first.1 with
    | nil => rfl
    | cons point points induction =>
        simp only [List.map_cons]
        rw [induction]
        congr 1
        apply Prod.ext <;>
          simp [periodTranslation, Cell.add, Cell.scale]
  rwa [zeroTranslate] at avoids

/-- Complete lifted separation is equivalent to checking only one relative
periodic translate for each pair of stored routes. -/
theorem liftedRoutesAvoidEachOther_iff_relative
    (drawing : PeriodicGridDrawing) :
    drawing.LiftedRoutesAvoidEachOther ↔
      drawing.RelativeLiftedRoutesAvoidEachOther := by
  constructor
  · intro separated first firstMember second secondMember
      relativeTranslate occurrencesDifferent
    have avoids :=
      separated first firstMember second secondMember
        (0, 0) relativeTranslate occurrencesDifferent
    have zeroTranslate :
        first.1.map
            (Cell.add (drawing.periodTranslation (0, 0))) =
          first.1 := by
      induction first.1 with
      | nil => rfl
      | cons point points induction =>
          simp only [List.map_cons]
          rw [induction]
          congr 1
          apply Prod.ext <;>
            simp [periodTranslation, Cell.add, Cell.scale]
    rwa [zeroTranslate] at avoids
  · intro separated first firstMember second secondMember
      firstTranslate secondTranslate occurrencesDifferent
    let relativeTranslate :=
      Cell.sub secondTranslate firstTranslate
    have relativeOccurrencesDifferent :
        (first.2, (0, 0)) ≠
          (second.2, relativeTranslate) := by
      intro equal
      apply occurrencesDifferent
      have indicesEqual : first.2 = second.2 :=
        congrArg (fun occurrence : Nat × Cell => occurrence.1) equal
      have relativeZero : (0, 0) = relativeTranslate :=
        congrArg (fun occurrence : Nat × Cell => occurrence.2) equal
      apply Prod.ext indicesEqual
      rcases firstTranslate with ⟨firstX, firstY⟩
      rcases secondTranslate with ⟨secondX, secondY⟩
      simp only [relativeTranslate, Cell.sub, Prod.mk.injEq] at relativeZero
      simp only [Prod.mk.injEq]
      constructor <;> omega
    have relativeAvoids :=
      separated first firstMember second secondMember
        relativeTranslate relativeOccurrencesDifferent
    have translatedAvoids :=
      routesAvoidEachOther_translate relativeAvoids
        (drawing.periodTranslation firstTranslate)
    have secondTranslation :
        (second.1.map
            (Cell.add
              (drawing.periodTranslation relativeTranslate))).map
            (Cell.add
              (drawing.periodTranslation firstTranslate)) =
          second.1.map
            (Cell.add
              (drawing.periodTranslation secondTranslate)) := by
      simp only [List.map_map]
      apply List.map_congr_left
      intro point pointMember
      rcases point with ⟨pointX, pointY⟩
      apply Prod.ext <;>
        simp [periodTranslation, relativeTranslate,
          Cell.add, Cell.sub, Cell.scale] <;>
        ring
    rwa [secondTranslation] at translatedAvoids

private theorem tagged_eq_of_mem_zipIdx_of_snd_eq
    {Item : Type*} {items : List Item}
    {first second : Item × Nat}
    (firstMember : first ∈ items.zipIdx)
    (secondMember : second ∈ items.zipIdx)
    (indicesEqual : first.2 = second.2) :
    first = second := by
  apply Prod.ext
  · have firstAt := (List.mem_zipIdx_iff_getElem?).mp firstMember
    have secondAt := (List.mem_zipIdx_iff_getElem?).mp secondMember
    rw [indicesEqual, secondAt] at firstAt
    exact Option.some.inj firstAt.symm
  · exact indicesEqual

private theorem routePointIsEndpoint_of_map_add
    {route : List Cell} {point offset : Cell}
    (endpoint :
      RoutePointIsEndpoint
        (route.map (Cell.add offset))
        (Cell.add offset point)) :
    RoutePointIsEndpoint route point := by
  rcases endpoint with head | last
  · left
    simp only [List.head?_map] at head
    rcases routeHead : route.head? with _ | routePoint
    · simp [routeHead] at head
    · rw [routeHead] at head
      simp only [Option.map_some, Option.some.injEq] at head
      have pointEqual : routePoint = point :=
        cell_add_left_injective offset head
      simpa [pointEqual] using routeHead
  · right
    simp only [List.getLast?_map] at last
    rcases routeLast : route.getLast? with _ | routePoint
    · simp [routeLast] at last
    · rw [routeLast] at last
      simp only [Option.map_some, Option.some.injEq] at last
      have pointEqual : routePoint = point :=
        cell_add_left_injective offset last
      simpa [pointEqual] using routeLast

/-- Pairwise avoidance of distinct lifted route occurrences, plus local
route simplicity for the same occurrence, gives the drawing's global
endpoint-only listed-point contact certificate. -/
theorem routePointsMeetOnlyAtEndpoints_of_liftedRoutesAvoidEachOther
    {drawing : PeriodicGridDrawing}
    (separated : drawing.LiftedRoutesAvoidEachOther)
    (simple :
      ∀ route ∈ drawing.edgeRoutes,
        LocalIncidenceDrawing.RouteIsSimple route) :
    drawing.RoutePointsMeetOnlyAtEndpoints := by
  intro first firstMember second secondMember
    firstTranslate secondTranslate keysDifferent pointsEqual
  unfold indexedRoutePoints at firstMember secondMember
  rcases List.mem_flatMap.mp firstMember with
    ⟨firstRoute, firstRouteMember, firstPointMember⟩
  rcases List.mem_map.mp firstPointMember with
    ⟨firstPoint, firstPointMember, firstEqual⟩
  have firstPointTaggedMember :
      firstPoint ∈ firstRoute.1.zipIdx :=
    firstPointMember
  subst first
  rcases List.mem_flatMap.mp secondMember with
    ⟨secondRoute, secondRouteMember, secondPointMember⟩
  rcases List.mem_map.mp secondPointMember with
    ⟨secondPoint, secondPointMember, secondEqual⟩
  have secondPointTaggedMember :
      secondPoint ∈ secondRoute.1.zipIdx :=
    secondPointMember
  subst second
  by_cases occurrencesDifferent :
      (firstRoute.2, firstTranslate) ≠
        (secondRoute.2, secondTranslate)
  · have avoids :=
      separated firstRoute firstRouteMember
        secondRoute secondRouteMember
        firstTranslate secondTranslate occurrencesDifferent
    have firstPointIndexLt : firstPoint.2 < firstRoute.1.length :=
      List.snd_lt_of_mem_zipIdx firstPointTaggedMember
    have secondPointIndexLt : secondPoint.2 < secondRoute.1.length :=
      List.snd_lt_of_mem_zipIdx secondPointTaggedMember
    let firstPointIndex : Fin firstRoute.1.length :=
      ⟨firstPoint.2, firstPointIndexLt⟩
    let secondPointIndex : Fin secondRoute.1.length :=
      ⟨secondPoint.2, secondPointIndexLt⟩
    have firstPointAt :
        firstRoute.1.get firstPointIndex = firstPoint.1 :=
      (List.getElem?_eq_some_iff.mp
        ((List.mem_zipIdx_iff_getElem?).mp firstPointTaggedMember)).2
    have secondPointAt :
        secondRoute.1.get secondPointIndex = secondPoint.1 :=
      (List.getElem?_eq_some_iff.mp
        ((List.mem_zipIdx_iff_getElem?).mp secondPointTaggedMember)).2
    have translatedPointsEqual :
        (firstRoute.1.map
          (Cell.add
            (drawing.periodTranslation firstTranslate))).get
              ⟨firstPoint.2, by simpa using firstPointIndexLt⟩ =
          (secondRoute.1.map
            (Cell.add
              (drawing.periodTranslation secondTranslate))).get
                ⟨secondPoint.2, by simpa using secondPointIndexLt⟩ := by
      have firstGetElem :
          firstRoute.1[firstPoint.2] = firstPoint.1 := by
        simpa [firstPointIndex, List.get_eq_getElem] using firstPointAt
      have secondGetElem :
          secondRoute.1[secondPoint.2] = secondPoint.1 := by
        simpa [secondPointIndex, List.get_eq_getElem] using secondPointAt
      simp only [List.get_eq_getElem, List.getElem_map]
      rw [firstGetElem, secondGetElem]
      simpa [Cell.add, add_comm] using pointsEqual
    have endpoints :=
      avoids.2.2.2
        ⟨firstPoint.2, by simpa using firstPointIndexLt⟩
        ⟨secondPoint.2, by simpa using secondPointIndexLt⟩
        translatedPointsEqual
    constructor
    · apply
        indexedRoutePoint_isEndpoint_of_routePointIsEndpoint
          (simple firstRoute.1
            (List.fst_mem_of_mem_zipIdx firstRouteMember)).1
          firstPointTaggedMember
      apply routePointIsEndpoint_of_map_add
        (offset := drawing.periodTranslation firstTranslate)
      have getElemEqual :
          firstRoute.1[firstPoint.2] = firstPoint.1 := by
        simpa [firstPointIndex, List.get_eq_getElem] using firstPointAt
      simpa [getElemEqual] using endpoints.1
    · apply
        indexedRoutePoint_isEndpoint_of_routePointIsEndpoint
          (simple secondRoute.1
            (List.fst_mem_of_mem_zipIdx secondRouteMember)).1
          secondPointTaggedMember
      apply routePointIsEndpoint_of_map_add
        (offset := drawing.periodTranslation secondTranslate)
      have getElemEqual :
          secondRoute.1[secondPoint.2] = secondPoint.1 := by
        simpa [secondPointIndex, List.get_eq_getElem] using secondPointAt
      simpa [getElemEqual] using endpoints.2
  · have occurrenceEqual :
        (firstRoute.2, firstTranslate) =
          (secondRoute.2, secondTranslate) :=
      not_ne_iff.mp occurrencesDifferent
    have routeEqual : firstRoute = secondRoute :=
      tagged_eq_of_mem_zipIdx_of_snd_eq
        firstRouteMember secondRouteMember
          (congrArg Prod.fst occurrenceEqual)
    subst secondRoute
    have translateEqual : firstTranslate = secondTranslate :=
      congrArg Prod.snd occurrenceEqual
    subst secondTranslate
    have pointValueEqual : firstPoint.1 = secondPoint.1 := by
      apply cell_add_left_injective
        (drawing.periodTranslation firstTranslate)
      simpa [Cell.add, add_comm] using pointsEqual
    have pointEqual : firstPoint = secondPoint :=
      tagged_eq_of_mem_zipIdx_of_snd_eq
        firstPointTaggedMember secondPointTaggedMember
        (by
          by_contra indicesDifferent
          have routeNodup :=
            (simple firstRoute.1
              (List.fst_mem_of_mem_zipIdx firstRouteMember)).1
          have firstAt :=
            (List.getElem?_eq_some_iff.mp
              ((List.mem_zipIdx_iff_getElem?).mp firstPointTaggedMember)).2
          have secondAt :=
            (List.getElem?_eq_some_iff.mp
              ((List.mem_zipIdx_iff_getElem?).mp secondPointTaggedMember)).2
          have firstLt := List.snd_lt_of_mem_zipIdx firstPointTaggedMember
          have secondLt := List.snd_lt_of_mem_zipIdx secondPointTaggedMember
          have indexEqual :
              (⟨firstPoint.2, firstLt⟩ : Fin firstRoute.1.length) =
                ⟨secondPoint.2, secondLt⟩ := by
            apply routeNodup.injective_get
            simpa using firstAt.trans
              (pointValueEqual.trans secondAt.symm)
          exact indicesDifferent (congrArg Fin.val indexEqual))
    subst secondPoint
    exact (keysDifferent rfl).elim

/-- Pairwise avoidance of distinct lifted route occurrences, plus local
route simplicity for the same occurrence, gives continuous disjointness of
all globally indexed route-segment interiors. -/
theorem routesHaveDisjointInteriors_of_liftedRoutesAvoidEachOther
    {drawing : PeriodicGridDrawing}
    (separated : drawing.LiftedRoutesAvoidEachOther)
    (simple :
      ∀ route ∈ drawing.edgeRoutes,
        LocalIncidenceDrawing.RouteIsSimple route) :
    drawing.RoutesHaveDisjointInteriors := by
  intro first firstMember second secondMember
    firstTranslate secondTranslate keysDifferent
  unfold indexedSegments at firstMember secondMember
  rcases List.mem_flatMap.mp firstMember with
    ⟨firstRoute, firstRouteMember, firstSegmentMember⟩
  rcases List.mem_map.mp firstSegmentMember with
    ⟨firstSegment, firstSegmentMember, firstEqual⟩
  have firstSegmentTaggedMember :
      firstSegment ∈ (gridPolylineSegments firstRoute.1).zipIdx :=
    firstSegmentMember
  subst first
  rcases List.mem_flatMap.mp secondMember with
    ⟨secondRoute, secondRouteMember, secondSegmentMember⟩
  rcases List.mem_map.mp secondSegmentMember with
    ⟨secondSegment, secondSegmentMember, secondEqual⟩
  have secondSegmentTaggedMember :
      secondSegment ∈ (gridPolylineSegments secondRoute.1).zipIdx :=
    secondSegmentMember
  subst second
  by_cases occurrencesDifferent :
      (firstRoute.2, firstTranslate) ≠
        (secondRoute.2, secondTranslate)
  · have avoids :=
      separated firstRoute firstRouteMember
        secondRoute secondRouteMember
        firstTranslate secondTranslate occurrencesDifferent
    have firstSegmentIndexLt :
        firstSegment.2 < (gridPolylineSegments firstRoute.1).length :=
      List.snd_lt_of_mem_zipIdx firstSegmentTaggedMember
    have secondSegmentIndexLt :
        secondSegment.2 < (gridPolylineSegments secondRoute.1).length :=
      List.snd_lt_of_mem_zipIdx secondSegmentTaggedMember
    let firstSegmentIndex :
        Fin (gridPolylineSegments firstRoute.1).length :=
      ⟨firstSegment.2, firstSegmentIndexLt⟩
    let secondSegmentIndex :
        Fin (gridPolylineSegments secondRoute.1).length :=
      ⟨secondSegment.2, secondSegmentIndexLt⟩
    have firstSegmentAt :
        (gridPolylineSegments firstRoute.1).get firstSegmentIndex =
          firstSegment.1 :=
      (List.getElem?_eq_some_iff.mp
        ((List.mem_zipIdx_iff_getElem?).mp
          firstSegmentTaggedMember)).2
    have secondSegmentAt :
        (gridPolylineSegments secondRoute.1).get secondSegmentIndex =
          secondSegment.1 :=
      (List.getElem?_eq_some_iff.mp
        ((List.mem_zipIdx_iff_getElem?).mp
          secondSegmentTaggedMember)).2
    have liftedAvoids :=
      avoids.1
        ⟨firstSegment.2, by
          simpa [gridPolylineSegments_map_add] using
            firstSegmentIndexLt⟩
        ⟨secondSegment.2, by
          simpa [gridPolylineSegments_map_add] using
            secondSegmentIndexLt⟩
    have firstSegmentElem :
        (gridPolylineSegments firstRoute.1)[firstSegment.2] =
          firstSegment.1 := by
      simpa [firstSegmentIndex, List.get_eq_getElem] using
        firstSegmentAt
    have secondSegmentElem :
        (gridPolylineSegments secondRoute.1)[secondSegment.2] =
          secondSegment.1 := by
      simpa [secondSegmentIndex, List.get_eq_getElem] using
        secondSegmentAt
    simpa [gridPolylineSegments_map_add,
      firstSegmentElem, secondSegmentElem]
      using liftedAvoids
  · have occurrenceEqual :
        (firstRoute.2, firstTranslate) =
          (secondRoute.2, secondTranslate) :=
      not_ne_iff.mp occurrencesDifferent
    have routeEqual : firstRoute = secondRoute :=
      tagged_eq_of_mem_zipIdx_of_snd_eq
        firstRouteMember secondRouteMember
          (congrArg Prod.fst occurrenceEqual)
    subst secondRoute
    have translateEqual : firstTranslate = secondTranslate :=
      congrArg Prod.snd occurrenceEqual
    subst secondTranslate
    have segmentIndicesDifferent :
        firstSegment.2 ≠ secondSegment.2 := by
      intro indicesEqual
      have segmentEqual : firstSegment = secondSegment :=
        tagged_eq_of_mem_zipIdx_of_snd_eq
          firstSegmentTaggedMember secondSegmentTaggedMember
          indicesEqual
      subst secondSegment
      exact keysDifferent rfl
    intro translatedMeet
    have baseMeet :
        GridSegment.InteriorsMeet firstSegment.1 secondSegment.1 :=
      (GridSegment.interiorsMeet_translate_both_iff
        firstSegment.1 secondSegment.1
        (drawing.periodTranslation firstTranslate)).mp
          translatedMeet
    exact
      (simple firstRoute.1
        (List.fst_mem_of_mem_zipIdx firstRouteMember)).2.2
          firstSegment firstSegmentTaggedMember
          secondSegment secondSegmentTaggedMember
          segmentIndicesDifferent baseMeet

/-- Complete lifted-route separation supplies continuous planarity as soon
as the stored drawing has unit steps (which already imply the established
integer-grid planarity predicate). -/
theorem isContinuouslyPlanar_of_liftedRoutesAvoidEachOther
    {drawing : PeriodicGridDrawing}
    (separated : drawing.LiftedRoutesAvoidEachOther)
    (simple :
      ∀ route ∈ drawing.edgeRoutes,
        LocalIncidenceDrawing.RouteIsSimple route)
    (unitSteps : drawing.HasUnitSteps) :
    drawing.IsContinuouslyPlanar :=
  ⟨isPlanar_of_hasUnitSteps unitSteps,
    routesHaveDisjointInteriors_of_liftedRoutesAvoidEachOther
      separated simple⟩

/-- The pairwise lifted-route interface packages both global geometric
predicates required for ribbon readiness. -/
theorem isRibbonReady_of_liftedRoutesAvoidEachOther
    {drawing : PeriodicGridDrawing}
    (separated : drawing.LiftedRoutesAvoidEachOther)
    (simple :
      ∀ route ∈ drawing.edgeRoutes,
        LocalIncidenceDrawing.RouteIsSimple route)
    (unitSteps : drawing.HasUnitSteps) :
    drawing.IsRibbonReady :=
  ⟨isContinuouslyPlanar_of_liftedRoutesAvoidEachOther
      separated simple unitSteps,
    routePointsMeetOnlyAtEndpoints_of_liftedRoutesAvoidEachOther
      separated simple⟩

/-- Relative-shift separation is the minimal pairwise hypothesis needed for
ribbon readiness; the absolute shifts are restored by common translation. -/
theorem isRibbonReady_of_relativeLiftedRoutesAvoidEachOther
    {drawing : PeriodicGridDrawing}
    (separated : drawing.RelativeLiftedRoutesAvoidEachOther)
    (simple :
      ∀ route ∈ drawing.edgeRoutes,
        LocalIncidenceDrawing.RouteIsSimple route)
    (unitSteps : drawing.HasUnitSteps) :
    drawing.IsRibbonReady :=
  isRibbonReady_of_liftedRoutesAvoidEachOther
    ((liftedRoutesAvoidEachOther_iff_relative drawing).mpr separated)
    simple unitSteps

end PeriodicGridDrawing
end LeanTrominoes
