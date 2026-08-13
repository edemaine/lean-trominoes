/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationAssignmentLookup
import LeanTrominoes.PeriodicThreeDMVertexNormalizationDrawing
import LeanTrominoes.PeriodicGridDrawingEndpointContacts
import LeanTrominoes.PeriodicGridDrawingVertexCoverage

/-!
# Geometric meaning of normalized 3DM assignments

The rasterizer stores vertex centers followed by the internal points of every
normalized route.  This module exposes that underlying geometric point list
and proves that assignment locations are exactly its image on the final
torus.  It also characterizes equality after rasterization as equality of two
points up to a period translation.

These facts form the bridge from the normalized drawing's separation
certificates to `FinalAssignmentsCollisionFree`.
-/

namespace LeanTrominoes

open Gadget

namespace PeriodicThreeDM

/-- The internal listed points of a route, excluding its first and last
points. -/
def routeInteriorPoints (route : List Cell) : List Cell :=
  route.tail.dropLast

/-- Forgetting the cell types emitted by the route rasterizer leaves exactly
the rasterized internal route points. -/
theorem routeInteriorAssignmentLocations
    (period : Nat) (color : WireColor) :
    ∀ route,
      (routeInteriorAssignments period color route).map Prod.fst =
        (routeInteriorPoints route).map (rasterLocation period)
  | [] => by simp [routeInteriorAssignments, routeInteriorPoints]
  | [_] => by simp [routeInteriorAssignments, routeInteriorPoints]
  | [_, _] => by simp [routeInteriorAssignments, routeInteriorPoints]
  | before :: current :: after :: rest => by
      simp only [routeInteriorAssignments, List.map_cons,
        routeInteriorPoints, List.tail_cons, List.dropLast_cons_cons]
      rw [routeInteriorAssignmentLocations period color
        (current :: after :: rest)]
      rfl

/-- Geometric points represented by the complete normalized assignment list,
in the same vertex-then-route order. -/
def PlanarPresentation.finalGeometricAssignmentPoints
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) : List Cell :=
  presentation.finalNormalizedVertexPositions ++
    problem.contractedEdges.flatMap fun edge =>
      routeInteriorPoints (presentation.finalNormalizationRoute edge)

/-- Assignment locations are exactly the final geometric assignment points
reduced to the raster torus. -/
theorem PlanarPresentation.finalAssignmentLocations_eq_map
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) :
    presentation.finalAssignmentLocations =
      presentation.finalGeometricAssignmentPoints.map
        (rasterLocation presentation.finalNormalizationPeriod) := by
  unfold PlanarPresentation.finalAssignmentLocations
    PlanarPresentation.finalCellAssignments
    PlanarPresentation.finalVertexAssignments
    PlanarPresentation.finalRouteAssignments
    PlanarPresentation.finalGeometricAssignmentPoints
  rw [presentation.finalNormalizedVertexPositions_eq_map]
  simp only [List.map_append, List.map_map, List.map_flatMap]
  congr 1
  apply List.flatMap_congr
  intro edge edgeMember
  exact routeInteriorAssignmentLocations _ _ _

/-- Two geometric points have the same raster location exactly when one is a
period translate of the other. -/
theorem rasterLocation_eq_iff_exists_periodTranslation
    (period : Nat) (first second : Cell) :
    rasterLocation period first = rasterLocation period second ↔
      ∃ translate : Cell,
        first = Cell.add second
          (Cell.scale (period : Int) translate) := by
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  constructor
  · intro equal
    simp only [rasterLocation, Prod.mk.injEq] at equal
    have horizontalMod :
        firstX ≡ secondX [ZMOD (period : Int)] := equal.1
    have negVerticalMod :
        -firstY ≡ -secondY [ZMOD (period : Int)] := equal.2
    have verticalMod :
        firstY ≡ secondY [ZMOD (period : Int)] :=
      Int.neg_modEq_neg.mp negVerticalMod
    rcases Int.modEq_iff_add_fac.mp horizontalMod with
      ⟨horizontalTranslate, horizontalEqual⟩
    rcases Int.modEq_iff_add_fac.mp verticalMod with
      ⟨verticalTranslate, verticalEqual⟩
    refine ⟨(-horizontalTranslate, -verticalTranslate), ?_⟩
    simp only [Cell.add, Cell.scale, Prod.mk.injEq]
    constructor <;> nlinarith
  · rintro ⟨translate, equal⟩
    rw [equal]
    exact rasterLocation_add_period period (secondX, secondY) translate

/-- A finite geometric point list has neither literal duplicates nor distinct
points that become equal after translating by whole periods. -/
def PointsSeparatedModuloPeriod
    (period : Nat) (points : List Cell) : Prop :=
  points.Nodup ∧
    ∀ first ∈ points, ∀ second ∈ points,
      first ≠ second →
        ∀ translate : Cell,
          first ≠ Cell.add second
            (Cell.scale (period : Int) translate)

/-- Periodic geometric separation makes rasterization injective on a finite
point list. -/
theorem rasterLocations_nodup_of_pointsSeparatedModuloPeriod
    {period : Nat} {points : List Cell}
    (separated : PointsSeparatedModuloPeriod period points) :
    (points.map (rasterLocation period)).Nodup := by
  apply List.Nodup.map_on
  · intro first firstMember second secondMember equal
    by_contra different
    rcases
        (rasterLocation_eq_iff_exists_periodTranslation
          period first second).mp equal with
      ⟨translate, translatedEqual⟩
    exact separated.2 first firstMember second secondMember
      different translate translatedEqual
  · exact separated.1

/-- The remaining collision-freedom goal can be discharged entirely in the
geometric model, before any cell types are considered. -/
theorem PlanarPresentation.finalAssignmentsCollisionFree_of_pointsSeparated
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (separated : PointsSeparatedModuloPeriod
      presentation.finalNormalizationPeriod
      presentation.finalGeometricAssignmentPoints) :
    presentation.FinalAssignmentsCollisionFree := by
  unfold PlanarPresentation.FinalAssignmentsCollisionFree
  rw [presentation.finalAssignmentLocations_eq_map]
  exact rasterLocations_nodup_of_pointsSeparatedModuloPeriod separated

end PeriodicThreeDM

namespace PeriodicGridDrawing

open PeriodicThreeDM

/-- Stable identity of a point that receives a raster assignment: either a
stored vertex-position index or a stored route/interior-point index pair. -/
abbrev AssignmentPointKey := Nat ⊕ (Nat × Nat)

/-- Route-point occurrences that are strictly internal according to their
syntactic point indices.  Starting the inner enumeration at one makes these
indices agree with the original complete route. -/
def indexedInteriorRoutePoints (drawing : PeriodicGridDrawing) :
    List IndexedRoutePoint :=
  drawing.edgeRoutes.zipIdx.flatMap fun taggedRoute =>
    taggedRoute.1.tail.dropLast.zipIdx 1 |>.map fun taggedPoint =>
      { routeIndex := taggedRoute.2
        pointIndex := taggedPoint.2
        routeLength := taggedRoute.1.length
        point := taggedPoint.1 }

/-- Removing a final point preserves the tagged indices of every remaining
point. -/
private theorem zipIdx_dropLast_sublist :
    ∀ (points : List Cell) (start : Nat),
      List.Sublist (points.dropLast.zipIdx start) (points.zipIdx start)
  | [], _ => by simp
  | [_], _ => by simp
  | first :: second :: rest, start => by
      simp only [List.dropLast_cons_cons, List.zipIdx_cons]
      exact
        List.Sublist.cons_cons (first, start)
          (zipIdx_dropLast_sublist (second :: rest) (start + 1))

/-- Every directly enumerated internal occurrence also belongs to the
standard all-route-point enumeration. -/
theorem indexedInteriorRoutePoint_mem_indexedRoutePoints
    {drawing : PeriodicGridDrawing} {indexed : IndexedRoutePoint}
    (member : indexed ∈ drawing.indexedInteriorRoutePoints) :
    indexed ∈ drawing.indexedRoutePoints := by
  unfold indexedInteriorRoutePoints at member
  rcases List.mem_flatMap.mp member with
    ⟨taggedRoute, taggedRouteMember, indexedMember⟩
  rcases taggedRoute with ⟨route, routeIndex⟩
  rcases List.mem_map.mp indexedMember with
    ⟨taggedPoint, taggedPointMember, indexedEqual⟩
  subst indexed
  unfold indexedRoutePoints
  apply List.mem_flatMap.mpr
  refine ⟨(route, routeIndex), taggedRouteMember, ?_⟩
  apply List.mem_map.mpr
  refine ⟨taggedPoint, ?_, rfl⟩
  cases route with
  | nil => simp at taggedPointMember
  | cons first rest =>
      simp only [List.tail_cons] at taggedPointMember
      simp only [List.zipIdx_cons, List.mem_cons]
      right
      exact
        (zipIdx_dropLast_sublist rest 1).mem taggedPointMember

/-- A directly enumerated route-interior occurrence is syntactically neither
the first nor the last point of its route. -/
theorem indexedInteriorRoutePoint_not_endpoint
    {drawing : PeriodicGridDrawing} {indexed : IndexedRoutePoint}
    (member : indexed ∈ drawing.indexedInteriorRoutePoints) :
    ¬ indexed.IsEndpoint := by
  unfold indexedInteriorRoutePoints at member
  rcases List.mem_flatMap.mp member with
    ⟨taggedRoute, taggedRouteMember, indexedMember⟩
  rcases taggedRoute with ⟨route, routeIndex⟩
  rcases List.mem_map.mp indexedMember with
    ⟨taggedPoint, taggedPointMember, indexedEqual⟩
  subst indexed
  have shiftedMember := taggedPointMember
  rw [List.zipIdx_eq_map_add] at shiftedMember
  rcases List.mem_map.mp shiftedMember with
    ⟨localPoint, localPointMember, localEqual⟩
  rcases taggedPoint with ⟨point, pointIndex⟩
  rcases localPoint with ⟨localPoint, localIndex⟩
  simp only [Prod.mk.injEq] at localEqual
  rcases localEqual with ⟨pointEqual, indexEqual⟩
  subst point
  subst pointIndex
  have localIndexLt := List.snd_lt_of_mem_zipIdx localPointMember
  simp only [List.length_dropLast, List.length_tail] at localIndexLt
  unfold IndexedRoutePoint.IsEndpoint
  have pointIndexNonzero : 1 + localIndex ≠ 0 := by omega
  have pointIndexBeforeLast : 1 + localIndex + 1 < route.length := by
    omega
  exact fun endpoint => endpoint.elim pointIndexNonzero
    (Nat.ne_of_lt pointIndexBeforeLast)

/-- Every assignment-receiving geometric occurrence, with vertices before
route interiors just as in the rasterizer. -/
def indexedAssignmentPoints (drawing : PeriodicGridDrawing) :
    List (AssignmentPointKey × Cell) :=
  (drawing.vertexPositions.zipIdx.map fun taggedPosition =>
      (Sum.inl taggedPosition.2, taggedPosition.1)) ++
    drawing.indexedInteriorRoutePoints.map fun indexed =>
      (Sum.inr (indexed.routeIndex, indexed.pointIndex), indexed.point)

/-- The occurrence enumeration forgets to the expected vertex-plus-route
interior point list. -/
theorem indexedAssignmentPoints_map_point
    (drawing : PeriodicGridDrawing) :
    drawing.indexedAssignmentPoints.map Prod.snd =
      drawing.vertexPositions ++
        drawing.edgeRoutes.flatMap fun route => route.tail.dropLast := by
  unfold indexedAssignmentPoints indexedInteriorRoutePoints
  simp only [List.map_append, List.map_map, List.map_flatMap]
  change
    (drawing.vertexPositions.zipIdx.map Prod.fst) ++
        drawing.edgeRoutes.zipIdx.flatMap (fun taggedRoute =>
          taggedRoute.1.tail.dropLast.zipIdx 1 |>.map Prod.fst) =
      drawing.vertexPositions ++
        drawing.edgeRoutes.flatMap fun route => route.tail.dropLast
  rw [List.zipIdx_map_fst]
  simp_rw [List.zipIdx_map_fst]
  congr 1
  calc
    _ = (drawing.edgeRoutes.zipIdx.map Prod.fst).flatMap
        (fun route => route.tail.dropLast) := by
      symm
      rw [List.flatMap_map]
    _ = _ := by rw [List.zipIdx_map_fst]

/-- Point indices inside one route's `zipIdx` enumeration are unique even
when the route repeats a geometric point. -/
private theorem interiorPointKeys_nodup
    (routeIndex : Nat) (route : List Cell) :
    ((route.tail.dropLast.zipIdx 1).map fun taggedPoint =>
      (routeIndex, taggedPoint.2)).Nodup := by
  let taggedPoints := route.tail.dropLast.zipIdx 1
  have pointIndicesNodup : (taggedPoints.map Prod.snd).Nodup := by
    simp [taggedPoints, List.nodup_range']
  have taggedPointsNodup : taggedPoints.Nodup :=
    pointIndicesNodup.of_map Prod.snd
  apply List.Nodup.map_on
  · intro first firstMember second secondMember equal
    have pointIndicesEqual : first.2 = second.2 :=
      congrArg (fun key : Nat × Nat => key.2) equal
    exact
      ((List.nodup_map_iff_inj_on taggedPointsNodup).mp
        pointIndicesNodup)
      first firstMember second secondMember pointIndicesEqual
  · exact taggedPointsNodup

/-- Route-index/point-index keys are unique across every stored route
interior occurrence. -/
theorem indexedInteriorRoutePointKeys_nodup
    (drawing : PeriodicGridDrawing) :
    (drawing.indexedInteriorRoutePoints.map fun indexed =>
      (indexed.routeIndex, indexed.pointIndex)).Nodup := by
  unfold indexedInteriorRoutePoints
  rw [List.map_flatMap, List.nodup_flatMap]
  constructor
  · intro taggedRoute taggedRouteMember
    rw [List.map_map]
    change
      ((taggedRoute.1.tail.dropLast.zipIdx 1).map fun taggedPoint =>
        (taggedRoute.2, taggedPoint.2)).Nodup
    exact interiorPointKeys_nodup taggedRoute.2 taggedRoute.1
  · have routeIndicesPairwise :
        drawing.edgeRoutes.zipIdx.Pairwise
          (fun first second => first.2 ≠ second.2) := by
      rw [← List.pairwise_map]
      exact List.nodup_zipIdx_map_snd drawing.edgeRoutes
    apply routeIndicesPairwise.imp
    intro first second routeIndicesDifferent
    change List.Disjoint _ _
    rw [List.disjoint_left]
    intro key firstMember secondMember
    rcases List.mem_map.mp firstMember with
      ⟨firstPoint, firstPointMember, firstEqual⟩
    rcases List.mem_map.mp secondMember with
      ⟨secondPoint, secondPointMember, secondEqual⟩
    rcases List.mem_map.mp firstPointMember with
      ⟨firstTaggedPoint, firstTaggedPointMember, rfl⟩
    rcases List.mem_map.mp secondPointMember with
      ⟨secondTaggedPoint, secondTaggedPointMember, rfl⟩
    apply routeIndicesDifferent
    have routeIndexEqual :=
      congrArg Prod.fst (firstEqual.trans secondEqual.symm)
    simpa using routeIndexEqual

/-- All assignment-point keys are duplicate-free by construction. -/
theorem indexedAssignmentPointKeys_nodup
    (drawing : PeriodicGridDrawing) :
    (drawing.indexedAssignmentPoints.map Prod.fst).Nodup := by
  unfold indexedAssignmentPoints
  simp only [List.map_append, List.map_map]
  rw [List.nodup_append]
  refine ⟨?_, ?_, ?_⟩
  · change
      (drawing.vertexPositions.zipIdx.map fun taggedPosition =>
        Sum.inl taggedPosition.2).Nodup
    have mapped :=
      (List.nodup_zipIdx_map_snd drawing.vertexPositions).map
        (@Sum.inl_injective Nat (Nat × Nat))
    rw [List.map_map] at mapped
    simpa only [Function.comp_def] using mapped
  · change
      (drawing.indexedInteriorRoutePoints.map fun indexed =>
        Sum.inr (indexed.routeIndex, indexed.pointIndex)).Nodup
    have mapped := drawing.indexedInteriorRoutePointKeys_nodup.map
      (@Sum.inr_injective Nat (Nat × Nat))
    rw [List.map_map] at mapped
    simpa only [Function.comp_def] using mapped
  · intro key vertexMember routeKey routeMember equal
    rcases List.mem_map.mp vertexMember with
      ⟨vertex, vertexMember, vertexEqual⟩
    rcases List.mem_map.mp routeMember with
      ⟨routePoint, routePointMember, routeEqual⟩
    have impossible : Sum.inl vertex.2 =
        Sum.inr (routePoint.routeIndex, routePoint.pointIndex) := by
      exact vertexEqual.trans (equal.trans routeEqual.symm)
    cases impossible

/-- Rasterization is injective on the open fundamental square of a periodic
drawing. -/
theorem rasterLocation_injective_on_fundamentalSquare
    {drawing : PeriodicGridDrawing} {first second : Cell}
    (firstBounds : drawing.PositionInFundamentalSquare first)
    (secondBounds : drawing.PositionInFundamentalSquare second)
    (equal : rasterLocation drawing.gridSize first =
      rasterLocation drawing.gridSize second) :
    first = second := by
  rcases
      (rasterLocation_eq_iff_exists_periodTranslation
        drawing.gridSize first second).mp equal with
    ⟨translate, translatedEqual⟩
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  rcases translate with ⟨translateX, translateY⟩
  simp only [PositionInFundamentalSquare] at firstBounds secondBounds
  simp only [Cell.add, Cell.scale, Prod.mk.injEq] at translatedEqual
  have periodPositive : (0 : Int) < drawing.gridSize := by
    exact_mod_cast Nat.zero_lt_succ drawing.gridSizePred
  have translation_eq_zero
      (firstCoordinate secondCoordinate translationCoordinate : Int)
      (firstLower : 0 < firstCoordinate)
      (firstUpper : firstCoordinate < drawing.gridSize)
      (secondLower : 0 < secondCoordinate)
      (secondUpper : secondCoordinate < drawing.gridSize)
      (coordinateEqual : firstCoordinate =
        secondCoordinate + drawing.gridSize * translationCoordinate) :
      translationCoordinate = 0 := by
    by_cases nonnegative : 0 ≤ translationCoordinate
    · by_cases zero : translationCoordinate = 0
      · exact zero
      · have productNonnegative :
            0 ≤ (drawing.gridSize : Int) *
              (translationCoordinate - 1) :=
          mul_nonneg (le_of_lt periodPositive) (by omega)
        nlinarith
    · have productNonnegative :
          0 ≤ (drawing.gridSize : Int) *
            (-translationCoordinate - 1) :=
        mul_nonneg (le_of_lt periodPositive) (by omega)
      nlinarith
  have horizontalTranslationZero :=
    translation_eq_zero firstX secondX translateX
      firstBounds.1 firstBounds.2.1
      secondBounds.1 secondBounds.2.1 translatedEqual.1
  have verticalTranslationZero :=
    translation_eq_zero firstY secondY translateY
      firstBounds.2.2.1 firstBounds.2.2.2
      secondBounds.2.2.1 secondBounds.2.2.2 translatedEqual.2
  subst translateX
  subst translateY
  simp only [mul_zero, add_zero] at translatedEqual
  exact Prod.ext translatedEqual.1 translatedEqual.2

/-- The mixed separation obligation left after compatible vertex placement
and endpoint-only route contacts: no stored vertex and route-interior
occurrence have the same torus location. -/
def VertexAssignmentsAvoidRouteInteriors
    (drawing : PeriodicGridDrawing) : Prop :=
  ∀ vertex ∈ drawing.vertexPositions.zipIdx,
    ∀ routePoint ∈ drawing.indexedInteriorRoutePoints,
      rasterLocation drawing.gridSize vertex.1 ≠
        rasterLocation drawing.gridSize routePoint.point

/-- Endpoint coverage and endpoint-only route contacts exclude every mixed
vertex/route-interior raster collision. -/
theorem vertexAssignmentsAvoidRouteInteriors_of_endpointCoverage
    (drawing : PeriodicGridDrawing)
    (covered : drawing.VertexPositionsCoveredByRouteEndpoints)
    (endpointContacts : drawing.RoutePointsMeetOnlyAtEndpoints) :
    drawing.VertexAssignmentsAvoidRouteInteriors := by
  intro vertex vertexMember routePoint routePointMember locationsEqual
  have routePointAllMember :=
    indexedInteriorRoutePoint_mem_indexedRoutePoints routePointMember
  rcases covered vertex.1
      (List.fst_mem_of_mem_zipIdx vertexMember) with
    ⟨covering, coveringMember, coverTranslate,
      coveringEndpoint, coveredEq⟩
  rcases
      (rasterLocation_eq_iff_exists_periodTranslation
        drawing.gridSize vertex.1 routePoint.point).mp locationsEqual with
    ⟨routeTranslate, translatedEq⟩
  have translatedEq' :
      vertex.1 = Cell.add routePoint.point
        (drawing.periodTranslation routeTranslate) := by
    simpa [periodTranslation] using translatedEq
  have keysDifferent :
      RoutePointOccurrenceKey covering coverTranslate ≠
        RoutePointOccurrenceKey routePoint routeTranslate := by
    intro keysEqual
    have routeIndexEq :
        covering.routeIndex = routePoint.routeIndex :=
      congrArg (fun key => key.1) keysEqual
    have pointIndexEq :
        covering.pointIndex = routePoint.pointIndex :=
      congrArg (fun key => key.2.1) keysEqual
    have indexedEq : covering = routePoint :=
      indexedRoutePoint_eq_of_mem_of_indices_eq
        coveringMember routePointAllMember routeIndexEq pointIndexEq
    apply indexedInteriorRoutePoint_not_endpoint routePointMember
    rw [← indexedEq]
    exact coveringEndpoint
  have endpoints :=
    endpointContacts covering coveringMember routePoint routePointAllMember
      coverTranslate routeTranslate keysDifferent
      (coveredEq.symm.trans translatedEq')
  exact indexedInteriorRoutePoint_not_endpoint routePointMember endpoints.2

/-- Exact geometric condition needed for assignment rasterization: distinct
syntactic assignment occurrences have distinct torus locations. -/
def AssignmentPointOccurrencesSeparated
    (drawing : PeriodicGridDrawing) : Prop :=
  ∀ first ∈ drawing.indexedAssignmentPoints,
    ∀ second ∈ drawing.indexedAssignmentPoints,
      first.1 ≠ second.1 →
        rasterLocation drawing.gridSize first.2 ≠
          rasterLocation drawing.gridSize second.2

/-- Compatible fundamental-square vertices, endpoint-only route-point
contacts, and the mixed vertex/interior condition together prove complete
assignment-occurrence separation. -/
theorem assignmentPointOccurrencesSeparated_of_endpointContacts
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (compatible : drawing.IsCompatible graph)
    (endpointContacts : drawing.RoutePointsMeetOnlyAtEndpoints)
    (mixed : drawing.VertexAssignmentsAvoidRouteInteriors) :
    drawing.AssignmentPointOccurrencesSeparated := by
  intro first firstMember second secondMember keysDifferent locationsEqual
  simp only [indexedAssignmentPoints, List.mem_append] at firstMember secondMember
  rcases firstMember with firstVertexMember | firstRouteMember
  · rcases List.mem_map.mp firstVertexMember with
      ⟨firstVertex, firstVertexSourceMember, firstEqual⟩
    subst first
    rcases secondMember with secondVertexMember | secondRouteMember
    · rcases List.mem_map.mp secondVertexMember with
        ⟨secondVertex, secondVertexSourceMember, secondEqual⟩
      subst second
      have positionsEqual :=
        rasterLocation_injective_on_fundamentalSquare
          (compatible.2.2.2.2.1 firstVertex.1
            (List.fst_mem_of_mem_zipIdx firstVertexSourceMember))
          (compatible.2.2.2.2.1 secondVertex.1
            (List.fst_mem_of_mem_zipIdx secondVertexSourceMember))
          locationsEqual
      have verticesEqual :=
        PeriodicThreeDM.tagged_eq_of_mem_zipIdx_of_fst_eq_of_nodup
          compatible.2.2.2.1 firstVertexSourceMember
          secondVertexSourceMember
          positionsEqual
      apply keysDifferent
      simpa using congrArg Prod.snd verticesEqual
    · rcases List.mem_map.mp secondRouteMember with
        ⟨secondRoute, secondRouteSourceMember, secondEqual⟩
      subst second
      exact mixed firstVertex firstVertexSourceMember secondRoute
        secondRouteSourceMember locationsEqual
  · rcases List.mem_map.mp firstRouteMember with
      ⟨firstRoute, firstRouteSourceMember, firstEqual⟩
    subst first
    rcases secondMember with secondVertexMember | secondRouteMember
    · rcases List.mem_map.mp secondVertexMember with
        ⟨secondVertex, secondVertexSourceMember, secondEqual⟩
      subst second
      exact mixed secondVertex secondVertexSourceMember firstRoute
        firstRouteSourceMember locationsEqual.symm
    · rcases List.mem_map.mp secondRouteMember with
        ⟨secondRoute, secondRouteSourceMember, secondEqual⟩
      subst second
      have routePointKeysDifferent :
          (firstRoute.routeIndex, firstRoute.pointIndex) ≠
            (secondRoute.routeIndex, secondRoute.pointIndex) := by
        simpa using keysDifferent
      rcases
          (rasterLocation_eq_iff_exists_periodTranslation
            drawing.gridSize firstRoute.point secondRoute.point).mp
            locationsEqual with
        ⟨translate, pointEqual⟩
      have fullKeysDifferent :
          RoutePointOccurrenceKey firstRoute (0, 0) ≠
            RoutePointOccurrenceKey secondRoute translate := by
        intro equal
        apply routePointKeysDifferent
        simp only [RoutePointOccurrenceKey] at equal
        exact Prod.ext
          (congrArg (fun key => key.1) equal)
          (congrArg (fun key => key.2.1) equal)
      have endpoints :=
        endpointContacts firstRoute
          (indexedInteriorRoutePoint_mem_indexedRoutePoints
            firstRouteSourceMember)
          secondRoute
          (indexedInteriorRoutePoint_mem_indexedRoutePoints
            secondRouteSourceMember)
          (0, 0) translate fullKeysDifferent
          (by
            simpa [periodTranslation, Cell.scale, Cell.add] using
              pointEqual)
      exact (indexedInteriorRoutePoint_not_endpoint firstRouteSourceMember
        endpoints.1).elim

/-- Compatibility, incidence, and endpoint-only route contacts are enough
for complete assignment-occurrence separation; mixed vertex/interior
separation need not be supplied independently. -/
theorem assignmentPointOccurrencesSeparated_of_incident_endpointContacts
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (compatible : drawing.IsCompatible graph)
    (incident : EveryVertexIncident graph)
    (endpointContacts : drawing.RoutePointsMeetOnlyAtEndpoints) :
    drawing.AssignmentPointOccurrencesSeparated := by
  apply assignmentPointOccurrencesSeparated_of_endpointContacts
    compatible endpointContacts
  exact vertexAssignmentsAvoidRouteInteriors_of_endpointCoverage drawing
    (vertexPositionsCoveredByRouteEndpoints_of_compatible
      graph drawing compatible incident)
    endpointContacts

/-- Occurrence separation makes the raster locations of all assignment
points duplicate-free. -/
theorem assignmentPointRasterLocations_nodup
    {drawing : PeriodicGridDrawing}
    (separated : drawing.AssignmentPointOccurrencesSeparated) :
    ((drawing.indexedAssignmentPoints.map Prod.snd).map
      (rasterLocation drawing.gridSize)).Nodup := by
  have keysNodup := drawing.indexedAssignmentPointKeys_nodup
  have occurrencesNodup : drawing.indexedAssignmentPoints.Nodup :=
    keysNodup.of_map Prod.fst
  have keyInjective :=
    (List.nodup_map_iff_inj_on occurrencesNodup).mp keysNodup
  rw [List.map_map]
  apply List.Nodup.map_on
  · intro first firstMember second secondMember equal
    by_contra different
    have keysDifferent : first.1 ≠ second.1 := by
      intro keysEqual
      exact different
        (keyInjective first firstMember second secondMember keysEqual)
    exact separated first firstMember second secondMember
      keysDifferent equal
  · exact occurrencesNodup

end PeriodicGridDrawing

namespace PeriodicThreeDM

/-- The final normalized drawing's occurrence separation directly
discharges the rasterizer's collision-freedom obligation. -/
theorem ContinuousPlanarPresentation.finalAssignmentsCollisionFree_of_occurrencesSeparated
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (separated : presentation.finalNormalizedGridDrawing
      |>.AssignmentPointOccurrencesSeparated) :
    presentation.toPlanarPresentation.FinalAssignmentsCollisionFree := by
  unfold PlanarPresentation.FinalAssignmentsCollisionFree
  rw [presentation.toPlanarPresentation.finalAssignmentLocations_eq_map]
  have pointList :=
    presentation.toPlanarPresentation.finalNormalizedGridDrawing
      |>.indexedAssignmentPoints_map_point
  have pointListFinal :
      (presentation.toPlanarPresentation.finalNormalizedGridDrawing
          |>.indexedAssignmentPoints.map Prod.snd) =
        presentation.toPlanarPresentation.finalGeometricAssignmentPoints := by
    calc
      _ =
          presentation.toPlanarPresentation.finalNormalizedGridDrawing.vertexPositions ++
            presentation.toPlanarPresentation.finalNormalizedGridDrawing.edgeRoutes.flatMap
              fun route => route.tail.dropLast := pointList
      _ =
          presentation.toPlanarPresentation.finalNormalizedVertexPositions ++
            (problem.contractedEdges.map
              presentation.toPlanarPresentation.finalNormalizationRoute).flatMap
                fun route => route.tail.dropLast := by
        rw [presentation.toPlanarPresentation.finalNormalizedGridDrawing_edgeRoutes_eq_map]
        rfl
      _ = presentation.toPlanarPresentation.finalGeometricAssignmentPoints := by
        unfold PlanarPresentation.finalGeometricAssignmentPoints
        simp only [List.flatMap_map, routeInteriorPoints]
  rw [← pointListFinal]
  simpa only [presentation.toPlanarPresentation.finalNormalizedGridDrawing_gridSize]
    using PeriodicGridDrawing.assignmentPointRasterLocations_nodup separated

/-- For a restricted 3DM instance, endpoint-only contacts in the final
normalized drawing are the sole remaining geometric input needed for raster
assignment collision freedom. -/
theorem ContinuousPlanarPresentation.finalAssignmentsCollisionFree_of_endpointContacts
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (degree : problem.DegreeTwoOrThree)
    (endpointContacts :
      presentation.toPlanarPresentation.finalNormalizedGridDrawing
        |>.RoutePointsMeetOnlyAtEndpoints) :
    presentation.toPlanarPresentation.FinalAssignmentsCollisionFree := by
  apply presentation.finalAssignmentsCollisionFree_of_occurrencesSeparated
  exact
    PeriodicGridDrawing.assignmentPointOccurrencesSeparated_of_incident_endpointContacts
      problem.contractedGraph
      presentation.toPlanarPresentation.finalNormalizedGridDrawing
      presentation.toPlanarPresentation.finalNormalizedGridDrawing_isCompatible
      (contractedGraph_everyVertexIncident problem
        presentation.problemWellFormed degree)
      endpointContacts

end PeriodicThreeDM
end LeanTrominoes
