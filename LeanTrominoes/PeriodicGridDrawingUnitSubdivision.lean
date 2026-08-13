/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalPolylineUnitSubdivision

/-!
# Unit subdivision of periodic grid drawings

Once a periodic drawing is orthogonal, every route segment can be subdivided
into genuine unit grid steps without changing its endpoints, vertices, or
period.  A unit horizontal or vertical segment has no integer point in its
relative interior.  Consequently the project's integer-grid `IsPlanar`
obligations become automatic for a drawing whose routes consist of unit
steps.

This file packages that observation independently of the planar-SAT
construction.  Compatibility and orthogonality are preserved, while
planarity follows solely from the resulting unit-step certificate.
-/

namespace LeanTrominoes

namespace AxisDirection

/-- Translating a genuine unit step preserves its direction and length. -/
theorem IsUnitAxisStep.translate
    {source target : Cell}
    (unit : IsUnitAxisStep source target)
    (offset : Cell) :
    IsUnitAxisStep
      (Cell.add offset source)
      (Cell.add offset target) := by
  rcases unit with
    ⟨direction, genuine, rfl⟩
  exact
    ⟨direction, genuine, by
      rcases offset with ⟨offsetX, offsetY⟩
      rcases source with ⟨sourceX, sourceY⟩
      cases direction <;>
        simp [Cell.add, AxisDirection.step] <;>
        omega⟩

/-- No integer lattice point lies in the relative interior of a genuine
unit axis step. -/
theorem IsUnitAxisStep.not_interiorContains
    {source target point : Cell}
    (unit : IsUnitAxisStep source target) :
    ¬(GridSegment.mk source target).InteriorContains point := by
  rcases unit with
    ⟨direction, genuine, rfl⟩
  rcases source with ⟨sourceX, sourceY⟩
  rcases point with ⟨pointX, pointY⟩
  cases direction <;>
    simp_all [AxisDirection.IsGenuine,
      AxisDirection.step,
      GridSegment.InteriorContains,
      GridSegment.IsHorizontal,
      GridSegment.IsVertical,
      GridSegment.StrictlyBetween,
      Cell.add] <;>
    omega

/-- Pointwise segment form of a unit-step chain. -/
theorem unitSteps_iff_segments (points : List Cell) :
    points.IsChain IsUnitAxisStep ↔
      ∀ segment ∈ gridPolylineSegments points,
        IsUnitAxisStep segment.start segment.finish := by
  induction points using List.twoStepInduction with
  | nil | singleton =>
      simp [gridPolylineSegments]
  | cons_cons first second rest _ tailInduction =>
      constructor
      · intro chain segment segmentMember
        have parts :=
          (List.isChain_cons_cons.mp chain :
            IsUnitAxisStep first second ∧
              (second :: rest).IsChain IsUnitAxisStep)
        simp only [gridPolylineSegments,
          List.mem_cons] at segmentMember
        rcases segmentMember with rfl | segmentMember
        · exact parts.1
        · exact
            (tailInduction second).mp parts.2
              segment segmentMember
      · intro segments
        apply List.isChain_cons_cons.mpr
        constructor
        · exact
            segments (GridSegment.mk first second)
              (by simp [gridPolylineSegments])
        · apply (tailInduction second).mpr
          intro segment segmentMember
          exact
            segments segment
              (by
                exact
                  List.mem_cons_of_mem
                    (GridSegment.mk first second)
                    segmentMember)

end AxisDirection

namespace PeriodicGridDrawing

/-- Every stored route in a drawing consists of genuine unit axis steps. -/
def HasUnitSteps (drawing : PeriodicGridDrawing) : Prop :=
  ∀ route ∈ drawing.edgeRoutes,
    route.IsChain AxisDirection.IsUnitAxisStep

instance (drawing : PeriodicGridDrawing) :
    Decidable drawing.HasUnitSteps := by
  unfold HasUnitSteps
  infer_instance

/-- Replace every stored orthogonal route by its ordered unit subdivision. -/
def unitSubdivide (drawing : PeriodicGridDrawing) :
    PeriodicGridDrawing where
  gridSizePred := drawing.gridSizePred
  vertexPositions := drawing.vertexPositions
  edgeRoutes :=
    drawing.edgeRoutes.map
      AxisDirection.unitSubdividePolyline

@[simp]
theorem unitSubdivide_gridSize
    (drawing : PeriodicGridDrawing) :
    drawing.unitSubdivide.gridSize = drawing.gridSize :=
  rfl

@[simp]
theorem unitSubdivide_periodTranslation
    (drawing : PeriodicGridDrawing) (translate : Cell) :
    drawing.unitSubdivide.periodTranslation translate =
      drawing.periodTranslation translate :=
  rfl

@[simp]
theorem unitSubdivide_vertexPosition
    {Vertex : Type*} [BEq Vertex]
    (drawing : PeriodicGridDrawing)
    (graph : PeriodicGraph Vertex) (vertex : Vertex) :
    drawing.unitSubdivide.vertexPosition graph vertex =
      drawing.vertexPosition graph vertex :=
  rfl

@[simp]
theorem unitSubdivide_edgeRoute
    (drawing : PeriodicGridDrawing) (edgeIndex : Nat) :
    drawing.unitSubdivide.edgeRoute edgeIndex =
      AxisDirection.unitSubdividePolyline
        (drawing.edgeRoute edgeIndex) := by
  unfold unitSubdivide edgeRoute
  simpa only [AxisDirection.unitSubdividePolyline_nil] using
    (List.getD_map
      (l := drawing.edgeRoutes) (d := [])
      (n := edgeIndex)
      AxisDirection.unitSubdividePolyline)

/-- A tagged graph edge selects an actual stored route in every compatible
drawing. -/
theorem edgeRoute_mem_of_compatible
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing}
    (compatible : drawing.IsCompatible graph)
    {taggedEdge : PeriodicEdge Vertex × Nat}
    (edgeMember : taggedEdge ∈ graph.edges.zipIdx) :
    drawing.edgeRoute taggedEdge.2 ∈ drawing.edgeRoutes := by
  have edgeIndexLt :
      taggedEdge.2 < graph.edges.length :=
    List.snd_lt_of_mem_zipIdx edgeMember
  have routeIndexLt :
      taggedEdge.2 < drawing.edgeRoutes.length := by
    rwa [compatible.2.2.1]
  unfold edgeRoute
  rw [List.getD_eq_getElem _ _ routeIndexLt]
  exact List.get_mem drawing.edgeRoutes ⟨taggedEdge.2, routeIndexLt⟩

/-- Unit subdivision preserves exact graph-route endpoints. -/
theorem routesMatch_unitSubdivide
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (drawing : PeriodicGridDrawing)
    (compatible : drawing.IsCompatible graph)
    (orthogonal : drawing.IsOrthogonal) :
    drawing.unitSubdivide.RoutesMatch graph := by
  intro taggedEdge taggedEdgeMember
  have endpoints :=
    compatible.2.2.2.2.2 taggedEdge taggedEdgeMember
  have routeMember :=
    edgeRoute_mem_of_compatible compatible taggedEdgeMember
  have routeOrthogonal :=
    (isOrthogonal_iff_routes drawing).mp orthogonal
      _ routeMember
  have routeNonempty :
      drawing.edgeRoute taggedEdge.2 ≠ [] := by
    intro routeEmpty
    rw [routeEmpty] at endpoints
    simp at endpoints
  rw [unitSubdivide_edgeRoute]
  constructor
  · rw [AxisDirection.unitSubdividePolyline_head?
      routeNonempty]
    exact endpoints.1
  · rw [AxisDirection.unitSubdividePolyline_getLast?
      routeNonempty routeOrthogonal]
    exact endpoints.2

/-- Unit subdivision preserves complete graph compatibility. -/
theorem isCompatible_unitSubdivide
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (drawing : PeriodicGridDrawing)
    (compatible : drawing.IsCompatible graph)
    (orthogonal : drawing.IsOrthogonal) :
    drawing.unitSubdivide.IsCompatible graph := by
  rcases compatible with
    ⟨wellFormed, vertexLength, routeLength,
      verticesNodup, vertexBounds, routesMatch⟩
  refine
    ⟨wellFormed, vertexLength, ?_, verticesNodup,
      vertexBounds, ?_⟩
  · simpa [unitSubdivide] using routeLength
  · exact
      routesMatch_unitSubdivide graph drawing
        ⟨wellFormed, vertexLength, routeLength,
          verticesNodup, vertexBounds, routesMatch⟩
        orthogonal

/-- Unit subdivision preserves drawing orthogonality. -/
theorem isOrthogonal_unitSubdivide
    (drawing : PeriodicGridDrawing)
    (orthogonal : drawing.IsOrthogonal) :
    drawing.unitSubdivide.IsOrthogonal := by
  rw [isOrthogonal_iff_routes]
  intro subdividedRoute subdividedMember
  rw [unitSubdivide] at subdividedMember
  rcases List.mem_map.mp subdividedMember with
    ⟨route, routeMember, rfl⟩
  exact
    AxisDirection.unitSubdividePolyline_orthogonal
      ((isOrthogonal_iff_routes drawing).mp orthogonal
        route routeMember)

/-- Unit subdivision exposes a genuine unit-step certificate for every
stored route. -/
theorem hasUnitSteps_unitSubdivide
    (drawing : PeriodicGridDrawing)
    (orthogonal : drawing.IsOrthogonal) :
    drawing.unitSubdivide.HasUnitSteps := by
  intro subdividedRoute subdividedMember
  rw [unitSubdivide] at subdividedMember
  rcases List.mem_map.mp subdividedMember with
    ⟨route, routeMember, rfl⟩
  exact
    AxisDirection.unitSubdividePolyline_unitSteps
      ((isOrthogonal_iff_routes drawing).mp orthogonal
        route routeMember)

/-- Every indexed segment of a unit-step drawing is a genuine unit axis
step. -/
theorem unitStep_of_mem_indexedSegments
    {drawing : PeriodicGridDrawing}
    (unitSteps : drawing.HasUnitSteps)
    {indexed : IndexedGridSegment}
    (indexedMember : indexed ∈ drawing.indexedSegments) :
    AxisDirection.IsUnitAxisStep
      indexed.segment.start indexed.segment.finish := by
  unfold indexedSegments at indexedMember
  rcases List.mem_flatMap.mp indexedMember with
    ⟨taggedRoute, taggedRouteMember, indexedMember⟩
  rcases List.mem_map.mp indexedMember with
    ⟨taggedSegment, taggedSegmentMember, indexedEqual⟩
  subst indexed
  apply
    (AxisDirection.unitSteps_iff_segments
      taggedRoute.1).mp
      (unitSteps taggedRoute.1
        (List.fst_mem_of_mem_zipIdx taggedRouteMember))
  exact List.fst_mem_of_mem_zipIdx taggedSegmentMember

/-- Any periodic drawing made entirely of unit axis steps satisfies the
integer-grid planarity predicate. -/
theorem isPlanar_of_hasUnitSteps
    {drawing : PeriodicGridDrawing}
    (unitSteps : drawing.HasUnitSteps) :
    drawing.IsPlanar := by
  constructor
  · intro first firstMember second secondMember
      firstTranslate secondTranslate point different
      firstInterior
    have firstUnit :=
      unitStep_of_mem_indexedSegments
        unitSteps firstMember
    have translatedUnit :=
      firstUnit.translate
        (drawing.periodTranslation firstTranslate)
    exact
      (translatedUnit.not_interiorContains
        firstInterior).elim
  · intro vertexPosition vertexMember indexed indexedMember
      vertexTranslate routeTranslate
    have unit :=
      unitStep_of_mem_indexedSegments
        unitSteps indexedMember
    have translatedUnit :=
      unit.translate
        (drawing.periodTranslation routeTranslate)
    exact translatedUnit.not_interiorContains

/-- Every orthogonal periodic drawing becomes planar after unit
subdivision. -/
theorem isPlanar_unitSubdivide
    (drawing : PeriodicGridDrawing)
    (orthogonal : drawing.IsOrthogonal) :
    drawing.unitSubdivide.IsPlanar :=
  isPlanar_of_hasUnitSteps
    (hasUnitSteps_unitSubdivide drawing orthogonal)

end PeriodicGridDrawing
end LeanTrominoes
