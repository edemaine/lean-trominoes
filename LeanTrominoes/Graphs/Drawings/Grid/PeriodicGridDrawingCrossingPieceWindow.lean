/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingEdgePieceEnumeration

/-! # The finite crossing-piece window contains every crossing of a prototype edge -/
namespace LeanTrominoes.PeriodicGridDrawing
open PeriodicOrthocrossing

theorem liftedStraightSegment_start {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (compatible : drawing.IsCompatible graph)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx) (cell : Cell) :
    (drawing.liftedStraightSegment tagged.2 cell).start =
      Cell.add (drawing.vertexPosition graph tagged.1.source) (drawing.periodTranslation cell) := by
  have ends := compatible.2.2.2.2.2 tagged member
  change Cell.add (drawing.periodTranslation cell) ((drawing.edgeRoute tagged.2).head?.getD (0,0)) = _
  rw [ends.1]
  simp [Cell.add,add_comm]

theorem liftedStraightSegment_finish {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (compatible : drawing.IsCompatible graph)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx) (cell : Cell) :
    (drawing.liftedStraightSegment tagged.2 cell).finish =
      Cell.add (drawing.vertexPosition graph tagged.1.target) (drawing.periodTranslation (Cell.add cell tagged.1.offset)) := by
  have ends := compatible.2.2.2.2.2 tagged member
  change Cell.add (drawing.periodTranslation cell) ((drawing.edgeRoute tagged.2).getLast?.getD (0,0)) = _
  rw [ends.2]
  apply Prod.ext <;> simp [Cell.add,periodTranslation,Cell.scale] <;> ring

theorem prototypeStraightSegment_x_bounds {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (compatible : drawing.IsCompatible graph)
    (graphLocal : graph.IsLocal) {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx) :
    -(drawing.gridSize : Int) < (drawing.liftedStraightSegment tagged.2 (0,0)).start.1 ∧
      (drawing.liftedStraightSegment tagged.2 (0,0)).start.1 < 2*(drawing.gridSize : Int) ∧
      -(drawing.gridSize : Int) < (drawing.liftedStraightSegment tagged.2 (0,0)).finish.1 ∧
      (drawing.liftedStraightSegment tagged.2 (0,0)).finish.1 < 2*(drawing.gridSize : Int) := by
  have ends := compatible.1.2 tagged.1 (List.fst_mem_of_mem_zipIdx member)
  rcases compatible.2.2.2.2.1 _ (compatible.vertexPosition_mem ends.1) with ⟨sourcePositive,sourceBound,_,_⟩
  rcases compatible.2.2.2.2.1 _ (compatible.vertexPosition_mem ends.2) with ⟨targetPositive,targetBound,_,_⟩
  have localEdge := graphLocal tagged.1 (List.fst_mem_of_mem_zipIdx member)
  unfold PeriodicEdge.span at localEdge
  have lowerOffset : -1 ≤ tagged.1.offset.1 := by omega
  have upperOffset : tagged.1.offset.1 ≤ 1 := by omega
  have positive : (0 : Int) < drawing.gridSize := by exact_mod_cast Nat.zero_lt_succ drawing.gridSizePred
  rw [liftedStraightSegment_start compatible member,liftedStraightSegment_finish compatible member]
  simp only [Cell.add,periodTranslation,Cell.scale,mul_zero,add_zero,zero_add]
  constructor
  · omega
  constructor
  · omega
  constructor <;> nlinarith

theorem crossingEdgePiece_mem {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (compatible : drawing.IsCompatible graph)
    (graphLocal : graph.IsLocal) {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (line : Int) (crosses : (drawing.liftedStraightSegment tagged.2 (0,0)).CrossesVerticalLine line) :
    crossingEdgePiece graph drawing tagged.2 line ∈ crossingEdgePieces graph drawing tagged.2 := by
  have bounds := prototypeStraightSegment_x_bounds compatible graphLocal member
  have lineLower : -(drawing.gridSize : Int) ≤ line := by rcases crosses with forward | backward <;> omega
  have lineUpper : line ≤ 2*(drawing.gridSize : Int) := by rcases crosses with forward | backward <;> omega
  let code := (line+(drawing.gridSize : Int)).toNat
  have codeEqual : (code : Int) = line+(drawing.gridSize : Int) := Int.toNat_of_nonneg (by omega)
  have codeBound : code < 3*drawing.gridSize+1 := by omega
  apply List.mem_filterMap.mpr
  refine ⟨line,?_,?_⟩
  · change line ∈ (List.range (3*drawing.gridSize+1)).map (fun number : Nat => (number : Int)-(drawing.gridSize : Int))
    exact List.mem_map.mpr ⟨code,List.mem_range.mpr codeBound,by omega⟩
  · simp [crosses]

end LeanTrominoes.PeriodicGridDrawing
