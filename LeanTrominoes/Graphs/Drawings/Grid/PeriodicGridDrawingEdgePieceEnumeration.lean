/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingOrientedRectangleRoutes
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingPaddedIncidenceIsolation
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingPaddedCrossingRoutes

/-! # Finite executable lists of replacement pieces for a straight periodic edge -/
namespace LeanTrominoes.PeriodicGridDrawing
open PeriodicOrthocrossing GeneralVertexNormalization

structure EdgeRoutePiece where
  start : ℚ
  finish : ℚ
  route : List Cell
  deriving DecidableEq

def rectangleEdgePiece? {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (index column : Nat) (cell : Cell) : Option EdgeRoutePiece :=
  let parent := (index,Cell.scale (-1) cell)
  (rectangleParentChord graph drawing column parent).map fun keys =>
    { start := min (rectanglePortParentParameter graph drawing column parent keys.1) (rectanglePortParentParameter graph drawing column parent keys.2)
      finish := max (rectanglePortParentParameter graph drawing column parent keys.1) (rectanglePortParentParameter graph drawing column parent keys.2)
      route := translatePolyline (drawing.rectangleRouteOffset column cell)
        (orientedRectangleInputRoute graph drawing column parent keys.1 keys.2) }

def rectangleEdgePieces {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (index : Nat) : List EdgeRoutePiece :=
  (List.range drawing.gridSize).flatMap fun column => neighborTranslations.filterMap (rectangleEdgePiece? graph drawing index column)

def crossingEdgePiece {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing) (index : Nat) (line : Int) : EdgeRoutePiece :=
  let segment := drawing.liftedStraightSegment index (0,0)
  let first := segment.rationalXParameter ((line : ℚ)-columnPerturbation graph drawing)
  let last := segment.rationalXParameter ((line : ℚ)+columnPerturbation graph drawing)
  let route := paddedCrossingRoute graph drawing line (index,(0,0))
  { start := min first last
    finish := max first last
    route := if segment.start.1 < segment.finish.1 then route else route.reverse }

def crossingEdgePieces {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing) (index : Nat) : List EdgeRoutePiece :=
  ((List.range (3*drawing.gridSize+1)).map fun (line : Nat) => (line : Int)-(drawing.gridSize : Int)).filterMap fun line =>
    if (drawing.liftedStraightSegment index (0,0)).CrossesVerticalLine line then some (crossingEdgePiece graph drawing index line) else none

def edgeFanParameter {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing) (index : Nat) : ℚ :=
  let segment := drawing.liftedStraightSegment index (0,0)
  columnPerturbation graph drawing / |(segment.finish.1 : ℚ)-(segment.start.1 : ℚ)|

def sourceEdgePiece {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (tagged : PeriodicEdge Vertex × Nat) : EdgeRoutePiece :=
  { start := 0
    finish := edgeFanParameter graph drawing tagged.2
    route := paddedIncidenceRoute graph drawing (sourcePort tagged.1 tagged.2) }

def targetEdgePiece {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (tagged : PeriodicEdge Vertex × Nat) : EdgeRoutePiece :=
  { start := 1-edgeFanParameter graph drawing tagged.2
    finish := 1
    route := (liftedPaddedIncidenceRoute graph drawing (targetPort tagged.1 tagged.2) tagged.1.offset).reverse }

def nonverticalEdgePieces {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (tagged : PeriodicEdge Vertex × Nat) : List EdgeRoutePiece :=
  [sourceEdgePiece graph drawing tagged] ++ rectangleEdgePieces graph drawing tagged.2 ++
    crossingEdgePieces graph drawing tagged.2 ++ [targetEdgePiece graph drawing tagged]

theorem rectangleEdgePiece?_valid {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (index column : Nat) (cell : Cell) {piece : EdgeRoutePiece} (lookup : rectangleEdgePiece? graph drawing index column cell = some piece) :
    0 < piece.start ∧ piece.start < piece.finish ∧ piece.finish < 1 ∧
      GridPolyline.IsRealOpenSimple piece.route ∧ OrthogonalPolyline piece.route := by
  unfold rectangleEdgePiece? at lookup
  cases chord : rectangleParentChord graph drawing column (index,Cell.scale (-1) cell) with
  | none => simp [chord] at lookup
  | some keys =>
    have pieceEq := Option.some.inj (by simpa only [chord,Option.map_some] using lookup)
    subst piece
    have interval := rectangleParentChordInterval_bounds planar graphLocal straight column (index,Cell.scale (-1) cell) chord
    have positive := (rectangleParentChordInterval planar graphLocal straight column (index,Cell.scale (-1) cell) chord).positive
    have route := orientedRectangleInputRoute_valid planar degree graphLocal straight column (index,Cell.scale (-1) cell) chord
    exact ⟨interval.1,positive,interval.2,route.1.translate _,route.2.translate _⟩

theorem rectangleEdgePieces_valid {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (index : Nat) {piece : EdgeRoutePiece} (member : piece ∈ rectangleEdgePieces graph drawing index) :
    0 < piece.start ∧ piece.start < piece.finish ∧ piece.finish < 1 ∧
      GridPolyline.IsRealOpenSimple piece.route ∧ OrthogonalPolyline piece.route := by
  obtain ⟨column,_,member⟩ := List.mem_flatMap.mp member
  obtain ⟨cell,_,lookup⟩ := List.mem_filterMap.mp member
  exact rectangleEdgePiece?_valid planar degree graphLocal straight index column cell lookup

theorem crossingEdgePiece_route_valid {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing) (index : Nat) (line : Int) :
    GridPolyline.IsRealOpenSimple (crossingEdgePiece graph drawing index line).route ∧
      OrthogonalPolyline (crossingEdgePiece graph drawing index line).route := by
  have simple := paddedCrossingRoute_isRealOpenSimple graph drawing line (index,(0,0))
  have orthogonal := paddedCrossingRoute_orthogonal graph drawing line (index,(0,0))
  unfold crossingEdgePiece
  dsimp only
  split_ifs
  · exact ⟨simple,orthogonal⟩
  · exact ⟨simple.reverse,orthogonal.reverse⟩

theorem nonverticalEdgePieces_route_valid {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (tagged : PeriodicEdge Vertex × Nat) {piece : EdgeRoutePiece} (member : piece ∈ nonverticalEdgePieces graph drawing tagged) :
    GridPolyline.IsRealOpenSimple piece.route ∧ OrthogonalPolyline piece.route := by
  simp only [nonverticalEdgePieces,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with ((source | rectangle) | crossing) | target
  · subst piece
    exact ⟨paddedIncidenceRoute_isRealOpenSimple graph drawing _,paddedIncidenceRoute_orthogonal graph drawing _⟩
  · exact (rectangleEdgePieces_valid planar degree graphLocal straight tagged.2 rectangle).2.2.2
  · obtain ⟨line,_,lookup⟩ := List.mem_filterMap.mp crossing
    split_ifs at lookup with crosses
    · have equal := Option.some.inj lookup
      subst piece
      exact crossingEdgePiece_route_valid graph drawing tagged.2 line
  · subst piece
    exact ⟨(liftedPaddedIncidenceRoute_isRealOpenSimple graph drawing _ _).reverse,
      (liftedPaddedIncidenceRoute_orthogonal graph drawing _ _).reverse⟩

end LeanTrominoes.PeriodicGridDrawing
