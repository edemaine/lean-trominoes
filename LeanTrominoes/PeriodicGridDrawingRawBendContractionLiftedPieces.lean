/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRawBendContractionPieceSimplicity
import LeanTrominoes.GridPolylineRealRouteChainTranslation

/-! # Lifted joined cubic routes retain their original-piece provenance -/
namespace LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
open PeriodicGraph.BendSubdivision PeriodicOrthocrossing

noncomputable def liftedRefinedPiece {V : Type*} [DecidableEq V] (source : PeriodicGraph V)
    (drawing : PeriodicGridDrawing) (record : (Nat × Nat) × PeriodicEdge (Vertex V)) (copy : Cell) : List Cell :=
  (refinedPiece source drawing record).map (Cell.add (Cell.scale (cubicScale drawing*drawing.gridSize) copy))

theorem liftedRefinedPiece_eq {V : Type*} [DecidableEq V] (source : PeriodicGraph V)
    (drawing : PeriodicGridDrawing) (record : (Nat × Nat) × PeriodicEdge (Vertex V)) (copy : Cell) :
    liftedRefinedPiece source drawing record copy=liftedPieceRoute source drawing
      (record.2,recordIndex source drawing record) (Cell.add (sourceCell drawing record.2.source) copy) := by
  unfold liftedRefinedPiece refinedPiece liftedPieceRoute translatePolyline
  rw [List.map_map]
  apply List.map_congr_left
  intro point _
  apply Prod.ext <;> simp only [Function.comp_def,Cell.add,Cell.scale] <;> ring

theorem liftedRefinedPiece_endpoints {V : Type*} [DecidableEq V] (source : PeriodicGraph V)
    (drawing : PeriodicGridDrawing) (record : (Nat × Nat) × PeriodicEdge (Vertex V)) (copy : Cell) :
    (liftedRefinedPiece source drawing record copy).head?=some (Cell.scale (cubicScale drawing)
      ((absoluteSegment (position source drawing) drawing.gridSize (sourceCell drawing) record.2).translate
        (drawing.periodTranslation copy)).start) ∧
    (liftedRefinedPiece source drawing record copy).getLast?=some (Cell.scale (cubicScale drawing)
      ((absoluteSegment (position source drawing) drawing.gridSize (sourceCell drawing) record.2).translate
        (drawing.periodTranslation copy)).finish) := by
  have ends := refinedPiece_endpoints source drawing record
  simp only [liftedRefinedPiece,List.head?_map,List.getLast?_map,ends.1,ends.2,Option.map_some]
  constructor <;> apply congrArg some <;> apply Prod.ext <;>
    simp only [periodTranslation,GridSegment.translate,Cell.scale,Cell.add] <;> ring

theorem parentRecord_parent {V : Type*} {drawing : PeriodicGridDrawing}
    {parent : PeriodicEdge V × Nat} {record : (Nat × Nat) × PeriodicEdge (Vertex V)}
    (member : record ∈ parentRecords drawing parent) : record.1.1=parent.2 := by
  obtain ⟨piece,_,rfl⟩ := List.mem_map.mp member
  rfl

theorem liftedContractedRoute_contains {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing source)
    (degree : source.DegreeAtMost 4) {parent : PeriodicEdge V × Nat}
    (parentMember : parent ∈ source.edges.zipIdx) (copy : Cell) {p : ℝ × ℝ}
    (contains : GridPolyline.RealContains ((contractedRoute source drawing parent).map
      (Cell.add (Cell.scale (cubicScale drawing*drawing.gridSize) copy))) p) :
    ∃ record ∈ parentRecords drawing parent, GridPolyline.RealContains (liftedRefinedPiece source drawing record copy) p := by
  obtain ⟨route,member,routeContains⟩ := GridPolyline.joinRouteChain_map_contains
    (parentPieces_chain planar parentMember)
    (fun route member => (parentPieces_openSimple planar degree parentMember member).1) _ contains
  obtain ⟨record,recordMember,rfl⟩ := List.mem_map.mp member
  exact ⟨record,recordMember,routeContains⟩

end LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
