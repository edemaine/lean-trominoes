/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicGraph

/-!
# Periodic grid drawings

The paper draws periodic graphs on a rational grid.  After multiplying all
coordinates by the common grid size, a fundamental square has integer side
length `M`, and a lattice translation of the graph becomes translation by an
integer multiple of `M`.

This file records that scaled representation.  Routes are polygonal chains
of integer grid points.  Segment occurrences retain their route and segment
indices, so the orthocrossing predicate can distinguish two geometrically
coincident segments (which must be rejected) from one segment compared with
itself.
-/

namespace LeanTrominoes

/-- A closed straight segment between two integer-grid points. -/
structure GridSegment where
  start : Cell
  finish : Cell
  deriving DecidableEq, Repr

namespace GridSegment

/-- Product representation used by the standard computability encoding. -/
def equivData : GridSegment ≃ Cell × Cell where
  toFun segment := (segment.start, segment.finish)
  invFun data := ⟨data.1, data.2⟩
  left_inv segment := by cases segment; rfl
  right_inv _ := rfl

noncomputable instance : Primcodable GridSegment :=
  Primcodable.ofEquiv (Cell × Cell) equivData

/-- Translate both endpoints by an integer-grid vector. -/
def translate (offset : Cell) (segment : GridSegment) : GridSegment :=
  ⟨Cell.add offset segment.start, Cell.add offset segment.finish⟩

/-- A nondegenerate horizontal segment. -/
def IsHorizontal (segment : GridSegment) : Prop :=
  segment.start.2 = segment.finish.2 ∧
    segment.start.1 ≠ segment.finish.1

/-- A nondegenerate vertical segment. -/
def IsVertical (segment : GridSegment) : Prop :=
  segment.start.1 = segment.finish.1 ∧
    segment.start.2 ≠ segment.finish.2

/-- The two permitted directions of an orthogonal route. -/
def IsAxisAligned (segment : GridSegment) : Prop :=
  segment.IsHorizontal ∨ segment.IsVertical

instance (segment : GridSegment) : Decidable segment.IsHorizontal := by
  unfold IsHorizontal
  infer_instance

instance (segment : GridSegment) : Decidable segment.IsVertical := by
  unfold IsVertical
  infer_instance

instance (segment : GridSegment) : Decidable segment.IsAxisAligned := by
  unfold IsAxisAligned
  infer_instance

/-- Strict betweenness on the integer line, independent of endpoint order. -/
def StrictlyBetween (first last value : Int) : Prop :=
  (first < value ∧ value < last) ∨ (last < value ∧ value < first)

instance (first last value : Int) :
    Decidable (StrictlyBetween first last value) := by
  unfold StrictlyBetween
  infer_instance

/-- Closed betweenness on the integer line, independent of endpoint order. -/
def Between (first last value : Int) : Prop :=
  (first ≤ value ∧ value ≤ last) ∨ (last ≤ value ∧ value ≤ first)

instance (first last value : Int) :
    Decidable (Between first last value) := by
  unfold Between
  infer_instance

/-- A point lies in the relative interior of a horizontal or vertical
segment. -/
def InteriorContains (segment : GridSegment) (point : Cell) : Prop :=
  (segment.IsHorizontal ∧ point.2 = segment.start.2 ∧
      StrictlyBetween segment.start.1 segment.finish.1 point.1) ∨
    (segment.IsVertical ∧ point.1 = segment.start.1 ∧
      StrictlyBetween segment.start.2 segment.finish.2 point.2)

instance (segment : GridSegment) (point : Cell) :
    Decidable (segment.InteriorContains point) := by
  unfold InteriorContains
  infer_instance

/-- A point lies on a horizontal or vertical segment, including its
endpoints. -/
def Contains (segment : GridSegment) (point : Cell) : Prop :=
  (segment.IsHorizontal ∧ point.2 = segment.start.2 ∧
      Between segment.start.1 segment.finish.1 point.1) ∨
    (segment.IsVertical ∧ point.1 = segment.start.1 ∧
      Between segment.start.2 segment.finish.2 point.2)

instance (segment : GridSegment) (point : Cell) :
    Decidable (segment.Contains point) := by
  unfold Contains
  infer_instance

/-- Relative-interior containment implies closed containment. -/
theorem contains_of_interiorContains {segment : GridSegment} {point : Cell}
    (contains : segment.InteriorContains point) :
    segment.Contains point := by
  rcases contains with
      ⟨horizontal, same, between⟩ | ⟨vertical, same, between⟩
  · exact Or.inl ⟨horizontal, same, between.elim
      (fun bounds => Or.inl ⟨bounds.1.le, bounds.2.le⟩)
      (fun bounds => Or.inr ⟨bounds.1.le, bounds.2.le⟩)⟩
  · exact Or.inr ⟨vertical, same, between.elim
      (fun bounds => Or.inl ⟨bounds.1.le, bounds.2.le⟩)
      (fun bounds => Or.inr ⟨bounds.1.le, bounds.2.le⟩)⟩

/-- Two segment interiors cross properly at a point: one segment is
horizontal and the other vertical. -/
def ProperlyCrossesAt
    (first second : GridSegment) (point : Cell) : Prop :=
  first.InteriorContains point ∧ second.InteriorContains point ∧
    ((first.IsHorizontal ∧ second.IsVertical) ∨
      (first.IsVertical ∧ second.IsHorizontal))

instance (first second : GridSegment) (point : Cell) :
    Decidable (ProperlyCrossesAt first second point) := by
  unfold ProperlyCrossesAt
  infer_instance

theorem properlyCrossesAt_symm {first second : GridSegment} {point : Cell}
    (crosses : ProperlyCrossesAt first second point) :
    ProperlyCrossesAt second first point := by
  rcases crosses with ⟨firstContains, secondContains, axes⟩
  exact ⟨secondContains, firstContains, axes.elim
    (fun pair => Or.inr ⟨pair.2, pair.1⟩)
    (fun pair => Or.inl ⟨pair.2, pair.1⟩)⟩

theorem isHorizontal_translate (segment : GridSegment) (offset : Cell) :
    (segment.translate offset).IsHorizontal ↔ segment.IsHorizontal := by
  simp [translate, IsHorizontal, Cell.add]

theorem isVertical_translate (segment : GridSegment) (offset : Cell) :
    (segment.translate offset).IsVertical ↔ segment.IsVertical := by
  simp [translate, IsVertical, Cell.add]

theorem isAxisAligned_translate (segment : GridSegment) (offset : Cell) :
    (segment.translate offset).IsAxisAligned ↔ segment.IsAxisAligned := by
  rw [IsAxisAligned, IsAxisAligned, isHorizontal_translate,
    isVertical_translate]

end GridSegment

/-- Consecutive segments of a polygonal chain. -/
def gridPolylineSegments : List Cell → List GridSegment
  | first :: second :: rest =>
      ⟨first, second⟩ :: gridPolylineSegments (second :: rest)
  | _ => []

theorem gridPolylineSegments_length (points : List Cell) :
    (gridPolylineSegments points).length = points.length - 1 := by
  induction points using List.twoStepInduction with
  | nil | singleton => rfl
  | cons_cons first second rest _ tailInduction =>
      simp [gridPolylineSegments, tailInduction second]

/-- A segment together with its syntactic occurrence in the finite drawing
presentation. -/
structure IndexedGridSegment where
  routeIndex : Nat
  segmentIndex : Nat
  segment : GridSegment
  deriving DecidableEq, Repr

/-- A finite fundamental-domain presentation of a periodic grid drawing.
Vertex positions correspond in order to the graph's protovertices, and edge
routes correspond in order to its protoedges. -/
structure PeriodicGridDrawing where
  gridSizePred : Nat
  vertexPositions : List Cell
  edgeRoutes : List (List Cell)
  deriving DecidableEq, Repr

namespace PeriodicGridDrawing

/-- Product representation used by the standard computability encoding. -/
def equivData : PeriodicGridDrawing ≃
    Nat × List Cell × List (List Cell) where
  toFun drawing :=
    (drawing.gridSizePred, drawing.vertexPositions, drawing.edgeRoutes)
  invFun data :=
    ⟨data.1, data.2.1, data.2.2⟩
  left_inv drawing := by cases drawing; rfl
  right_inv data := by rcases data with ⟨size, positions, routes⟩; rfl

noncomputable instance : Primcodable PeriodicGridDrawing :=
  Primcodable.ofEquiv (Nat × List Cell × List (List Cell)) equivData

/-- Positive side length of the scaled fundamental square. -/
def gridSize (drawing : PeriodicGridDrawing) : Nat :=
  drawing.gridSizePred + 1

/-- Scale a graph-lattice translation into drawing-grid coordinates. -/
def periodTranslation (drawing : PeriodicGridDrawing) (translate : Cell) :
    Cell :=
  Cell.scale drawing.gridSize translate

/-- The stored position corresponding to a protovertex's index in the graph
presentation. -/
def vertexPosition {Vertex : Type*} [BEq Vertex]
    (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (vertex : Vertex) : Cell :=
  drawing.vertexPositions.getD (graph.vertices.idxOf vertex) (0, 0)

/-- The route corresponding to a protoedge index. -/
def edgeRoute (drawing : PeriodicGridDrawing) (edgeIndex : Nat) :
    List Cell :=
  drawing.edgeRoutes.getD edgeIndex []

/-- Every route segment, tagged by its route and within-route index. -/
def indexedSegments (drawing : PeriodicGridDrawing) :
    List IndexedGridSegment :=
  drawing.edgeRoutes.zipIdx.flatMap fun (route, routeIndex) =>
    (gridPolylineSegments route).zipIdx.map fun (segment, segmentIndex) =>
      ⟨routeIndex, segmentIndex, segment⟩

/-- A stored vertex lies strictly inside the fundamental square. -/
def PositionInFundamentalSquare (drawing : PeriodicGridDrawing)
    (position : Cell) : Prop :=
  0 < position.1 ∧ position.1 < drawing.gridSize ∧
    0 < position.2 ∧ position.2 < drawing.gridSize

/-- The first and last points of every route match the appropriately
translated positions of its protoedge endpoints. -/
def RoutesMatch {Vertex : Type*} [BEq Vertex]
    (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing) : Prop :=
  ∀ taggedEdge ∈ graph.edges.zipIdx,
    (drawing.edgeRoute taggedEdge.2).head? =
        some (drawing.vertexPosition graph taggedEdge.1.source) ∧
      (drawing.edgeRoute taggedEdge.2).getLast? =
        some (Cell.add
          (drawing.vertexPosition graph taggedEdge.1.target)
          (drawing.periodTranslation taggedEdge.1.offset))

/-- Basic finite-presentation validity, independent of crossing behavior. -/
def IsCompatible {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing) : Prop :=
  graph.IsWellFormed ∧
    drawing.vertexPositions.length = graph.vertices.length ∧
    drawing.edgeRoutes.length = graph.edges.length ∧
    drawing.vertexPositions.Nodup ∧
    (∀ position ∈ drawing.vertexPositions,
      drawing.PositionInFundamentalSquare position) ∧
    drawing.RoutesMatch graph

/-- Every finite route segment is horizontal or vertical. -/
def IsOrthogonal (drawing : PeriodicGridDrawing) : Prop :=
  ∀ indexed ∈ drawing.indexedSegments, indexed.segment.IsAxisAligned

/-- Identity of one segment occurrence in the infinite periodic lift. -/
def SegmentOccurrenceKey (indexed : IndexedGridSegment)
    (translate : Cell) : Nat × Nat × Cell :=
  (indexed.routeIndex, indexed.segmentIndex, translate)

/-- Every meeting of two distinct segment interiors, allowing arbitrary
periodic translates, is a proper horizontal/vertical crossing.  This rules
out overlaps, tangencies, and triple crossings once crossing points are
separately required to be unique. -/
def IsOrthocrossing (drawing : PeriodicGridDrawing) : Prop :=
  ∀ first ∈ drawing.indexedSegments,
    ∀ second ∈ drawing.indexedSegments,
      ∀ firstTranslate secondTranslate point,
        SegmentOccurrenceKey first firstTranslate ≠
            SegmentOccurrenceKey second secondTranslate →
          (first.segment.translate
              (drawing.periodTranslation firstTranslate)).InteriorContains
            point →
          (second.segment.translate
              (drawing.periodTranslation secondTranslate)).InteriorContains
            point →
          GridSegment.ProperlyCrossesAt
            (first.segment.translate
              (drawing.periodTranslation firstTranslate))
            (second.segment.translate
              (drawing.periodTranslation secondTranslate))
            point

/-- No segment interior in the infinite periodic lift meets any distinct
segment occurrence.  Quantifying over the ordered pair also excludes a
route endpoint from touching the interior of another route.  Shared route
and graph endpoints remain permitted. -/
def RoutesAvoidInteriors (drawing : PeriodicGridDrawing) : Prop :=
  ∀ first ∈ drawing.indexedSegments,
    ∀ second ∈ drawing.indexedSegments,
      ∀ firstTranslate secondTranslate point,
        SegmentOccurrenceKey first firstTranslate ≠
            SegmentOccurrenceKey second secondTranslate →
          (first.segment.translate
              (drawing.periodTranslation firstTranslate)).InteriorContains
            point →
          ¬(second.segment.translate
              (drawing.periodTranslation secondTranslate)).Contains point

/-- No lifted graph vertex lies in the relative interior of a lifted route
segment.  Incidence endpoints are allowed because they are segment
endpoints, not interior points. -/
def VerticesAvoidRouteInteriors
    (drawing : PeriodicGridDrawing) : Prop :=
  ∀ vertexPosition ∈ drawing.vertexPositions,
    ∀ indexed ∈ drawing.indexedSegments,
      ∀ vertexTranslate routeTranslate,
        ¬(indexed.segment.translate
            (drawing.periodTranslation routeTranslate)).InteriorContains
          (Cell.add vertexPosition
            (drawing.periodTranslation vertexTranslate))

/-- The geometric nonintersection conditions needed of a planar periodic
grid drawing.  Compatibility with a particular graph and orthogonality are
kept separate because both are independently useful. -/
def IsPlanar (drawing : PeriodicGridDrawing) : Prop :=
  drawing.RoutesAvoidInteriors ∧
    drawing.VerticesAvoidRouteInteriors

end PeriodicGridDrawing

end LeanTrominoes
