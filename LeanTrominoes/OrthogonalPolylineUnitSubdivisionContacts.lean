/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.EmbeddedCNFIncidenceDrawing
import LeanTrominoes.OrthogonalPolylineUnitSubdivision

/-!
# Contact provenance through unit subdivision

Unit subdivision introduces lattice points inside the original source
segments.  This file proves that every introduced point is either an original
listed route point or lies in one original segment interior.  Consequently,
complete continuous separation of two original orthogonal routes implies
that their unit subdivisions can share listed points only at their outer
endpoints.
-/

namespace LeanTrominoes
namespace AxisDirection

open PeriodicOrthocrossing

/-- Every generated unit-segment point is an original endpoint or lies in
the original segment's relative interior. -/
theorem unitSegmentPoints_mem_endpoint_or_interior
    {first second point : Cell}
    (aligned : (GridSegment.mk first second).IsAxisAligned)
    (pointMember : point ∈ unitSegmentPoints first second) :
    point = first ∨ point = second ∨
      (GridSegment.mk first second).InteriorContains point := by
  unfold unitSegmentPoints at pointMember
  rcases List.mem_map.mp pointMember with
    ⟨index, indexMember, pointEquation⟩
  have indexLt :
      index < segmentLength first second + 1 :=
    List.mem_range.mp indexMember
  have indexLe :
      index ≤ segmentLength first second := by
    omega
  by_cases indexZero : index = 0
  · left
    subst index
    simpa [Cell.add, Cell.scale] using pointEquation.symm
  by_cases indexLast :
      index = segmentLength first second
  · right
    left
    subst index
    rw [← pointEquation]
    exact add_length_step_eq_second_of_axisAligned aligned
  · right
    right
    have indexPositive : 0 < index := by omega
    have indexStrict :
        index < segmentLength first second := by
      omega
    have finishEquation :=
      add_length_step_eq_second_of_axisAligned aligned
    have genuine :=
      between_isGenuine_of_axisAligned aligned
    cases directionEquation : between first second <;>
      simp_all [IsGenuine]
    all_goals
      subst point
      rcases first with ⟨firstX, firstY⟩
      rcases second with ⟨secondX, secondY⟩
      simp only [step, Cell.add, Cell.scale, Prod.mk.injEq,
        GridSegment.InteriorContains,
        GridSegment.IsHorizontal, GridSegment.IsVertical,
        GridSegment.StrictlyBetween] at finishEquation ⊢
      omega

/-- Every point of an orthogonal route's unit subdivision has exact
provenance in the original polyline. -/
theorem unitSubdividePolyline_mem_original_or_segmentInterior
    {points : List Cell}
    (orthogonal : OrthogonalPolyline points)
    {point : Cell}
    (pointMember : point ∈ unitSubdividePolyline points) :
    point ∈ points ∨
      ∃ segment ∈ gridPolylineSegments points,
        segment.InteriorContains point := by
  induction points using List.twoStepInduction with
  | nil =>
      simp at pointMember
  | singleton only =>
      exact Or.inl (by simpa using pointMember)
  | cons_cons first second rest _ tailInduction =>
      have orthogonalParts :=
        (List.isChain_cons_cons.mp orthogonal :
          (GridSegment.mk first second).IsAxisAligned ∧
            OrthogonalPolyline (second :: rest))
      rw [unitSubdividePolyline, joinAtEndpoint,
        List.mem_append] at pointMember
      rcases pointMember with firstSegmentMember | tailMember
      · rcases
          unitSegmentPoints_mem_endpoint_or_interior
            orthogonalParts.1 firstSegmentMember with
          pointFirst | pointSecond | pointInterior
        · left
          simp [pointFirst]
        · left
          simp [pointSecond]
        · right
          exact
            ⟨GridSegment.mk first second, by
              simp [gridPolylineSegments], pointInterior⟩
      · have tailPointMember :
            point ∈
              unitSubdividePolyline (second :: rest) :=
          List.mem_of_mem_tail tailMember
        rcases
            tailInduction second orthogonalParts.2
              tailPointMember with
          originalMember | ⟨segment, segmentMember,
            pointInterior⟩
        · left
          simp only [List.mem_cons] at originalMember ⊢
          exact Or.inr originalMember
        · right
          exact
            ⟨segment, by
              simp only [gridPolylineSegments, List.mem_cons]
              exact Or.inr segmentMember,
              pointInterior⟩

end AxisDirection

namespace PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- An original advertised endpoint remains an advertised endpoint after
unit subdivision. -/
theorem routePointIsEndpoint_unitSubdividePolyline
    {route : List Cell} {point : Cell}
    (nonempty : route ≠ [])
    (orthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline route)
    (endpoint : RoutePointIsEndpoint route point) :
    RoutePointIsEndpoint
      (AxisDirection.unitSubdividePolyline route) point := by
  rcases endpoint with first | last
  · left
    rw [AxisDirection.unitSubdividePolyline_head? nonempty]
    exact first
  · right
    rw [AxisDirection.unitSubdividePolyline_getLast?
      nonempty orthogonal]
    exact last

/-- If two continuously separated original routes meet only at advertised
endpoints, then so do their unit subdivisions. -/
theorem routesMeetOnlyAtEndpoints_unitSubdividePolyline
    {first second : List Cell}
    (firstNonempty : first ≠ [])
    (secondNonempty : second ≠ [])
    (firstOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline first)
    (secondOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline second)
    (avoids : RoutesAvoidEachOther first second) :
    RoutesMeetOnlyAtEndpoints
      (AxisDirection.unitSubdividePolyline first)
      (AxisDirection.unitSubdividePolyline second) := by
  intro firstIndex secondIndex pointEqual
  let point :=
    (AxisDirection.unitSubdividePolyline first).get firstIndex
  have firstPointMember :
      point ∈ AxisDirection.unitSubdividePolyline first :=
    List.get_mem _ firstIndex
  have secondPointMember :
      point ∈ AxisDirection.unitSubdividePolyline second := by
    change
      (AxisDirection.unitSubdividePolyline first).get firstIndex ∈
        AxisDirection.unitSubdividePolyline second
    rw [pointEqual]
    exact List.get_mem _ secondIndex
  rw [← pointEqual]
  change
    RoutePointIsEndpoint
        (AxisDirection.unitSubdividePolyline first) point ∧
      RoutePointIsEndpoint
        (AxisDirection.unitSubdividePolyline second) point
  have firstProvenance :=
    AxisDirection.unitSubdividePolyline_mem_original_or_segmentInterior
      firstOrthogonal firstPointMember
  have secondProvenance :=
    AxisDirection.unitSubdividePolyline_mem_original_or_segmentInterior
      secondOrthogonal secondPointMember
  rcases firstProvenance with
      firstOriginal |
      ⟨firstSegment, firstSegmentMember,
        firstInterior⟩
  · rcases secondProvenance with
        secondOriginal |
        ⟨secondSegment, secondSegmentMember,
          secondInterior⟩
    · rcases List.mem_iff_get.mp firstOriginal with
        ⟨firstOriginalIndex, firstOriginalEquation⟩
      rcases List.mem_iff_get.mp secondOriginal with
        ⟨secondOriginalIndex, secondOriginalEquation⟩
      have originalEndpoints :=
        avoids.2.2.2 firstOriginalIndex secondOriginalIndex
          (firstOriginalEquation.trans
            secondOriginalEquation.symm)
      rw [firstOriginalEquation,
        secondOriginalEquation] at originalEndpoints
      exact
        ⟨routePointIsEndpoint_unitSubdividePolyline
            firstNonempty firstOrthogonal originalEndpoints.1,
          routePointIsEndpoint_unitSubdividePolyline
            secondNonempty secondOrthogonal originalEndpoints.2⟩
    · rcases List.mem_iff_get.mp firstOriginal with
        ⟨firstOriginalIndex, firstOriginalEquation⟩
      rcases List.mem_iff_get.mp secondSegmentMember with
        ⟨secondSegmentIndex, secondSegmentEquation⟩
      have noInterior :=
        avoids.2.1 firstOriginalIndex secondSegmentIndex
      exact
        (noInterior (by
          rw [secondSegmentEquation,
            firstOriginalEquation]
          exact secondInterior)).elim
  · rcases secondProvenance with
        secondOriginal |
        ⟨secondSegment, secondSegmentMember,
          secondInterior⟩
    · rcases List.mem_iff_get.mp secondOriginal with
        ⟨secondOriginalIndex, secondOriginalEquation⟩
      rcases List.mem_iff_get.mp firstSegmentMember with
        ⟨firstSegmentIndex, firstSegmentEquation⟩
      have noInterior :=
        avoids.2.2.1 secondOriginalIndex firstSegmentIndex
      exact
        (noInterior (by
          rw [firstSegmentEquation,
            secondOriginalEquation]
          exact firstInterior)).elim
    · rcases List.mem_iff_get.mp firstSegmentMember with
        ⟨firstSegmentIndex, firstSegmentEquation⟩
      rcases List.mem_iff_get.mp secondSegmentMember with
        ⟨secondSegmentIndex, secondSegmentEquation⟩
      have interiorsDisjoint :=
        avoids.1 firstSegmentIndex secondSegmentIndex
      apply (interiorsDisjoint ?_).elim
      rw [firstSegmentEquation,
        secondSegmentEquation]
      exact
        GridSegment.interiorsMeet_of_interiorContains
          firstInterior secondInterior

/-- Strictly internal unit-subdivision points of two separated source
routes are distinct. -/
theorem internalUnitSubdividePolylinePoints_ne
    {first second : List Cell}
    (firstNonempty : first ≠ [])
    (secondNonempty : second ≠ [])
    (firstOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline first)
    (secondOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline second)
    (avoids : RoutesAvoidEachOther first second)
    {firstPoint secondPoint : Cell}
    (firstMember :
      firstPoint ∈
        AxisDirection.unitSubdividePolyline first)
    (secondMember :
      secondPoint ∈
        AxisDirection.unitSubdividePolyline second)
    (firstInternal :
      ¬RoutePointIsEndpoint
        (AxisDirection.unitSubdividePolyline first)
        firstPoint)
    (secondInternal :
      ¬RoutePointIsEndpoint
        (AxisDirection.unitSubdividePolyline second)
        secondPoint) :
    firstPoint ≠ secondPoint := by
  intro equal
  subst secondPoint
  rcases List.mem_iff_get.mp firstMember with
    ⟨firstIndex, firstEquation⟩
  rcases List.mem_iff_get.mp secondMember with
    ⟨secondIndex, secondEquation⟩
  have endpoints :=
    routesMeetOnlyAtEndpoints_unitSubdividePolyline
      firstNonempty secondNonempty
      firstOrthogonal secondOrthogonal avoids
      firstIndex secondIndex
      (firstEquation.trans secondEquation.symm)
  rw [firstEquation, secondEquation] at endpoints
  exact firstInternal endpoints.1

end PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
end LeanTrominoes
