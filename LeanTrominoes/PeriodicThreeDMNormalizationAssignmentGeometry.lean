import LeanTrominoes.PeriodicThreeDMNormalizationAssignmentLookup
import LeanTrominoes.PeriodicThreeDMVertexNormalizationDrawing
import LeanTrominoes.PeriodicGridDrawingEndpointContacts

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

/-- Exact geometric condition needed for assignment rasterization: distinct
syntactic assignment occurrences have distinct torus locations. -/
def AssignmentPointOccurrencesSeparated
    (drawing : PeriodicGridDrawing) : Prop :=
  ∀ first ∈ drawing.indexedAssignmentPoints,
    ∀ second ∈ drawing.indexedAssignmentPoints,
      first.1 ≠ second.1 →
        rasterLocation drawing.gridSize first.2 ≠
          rasterLocation drawing.gridSize second.2

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

end PeriodicThreeDM
end LeanTrominoes
