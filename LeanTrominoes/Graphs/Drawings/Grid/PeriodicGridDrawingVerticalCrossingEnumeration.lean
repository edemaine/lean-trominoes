/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingVerticalCrossings
import LeanTrominoes.Graphs.Drawings.Refinement.Straight.PeriodicGridDrawingStraightCopyWindow
import LeanTrominoes.Graphs.Core.PeriodicGraphDrawingCardinality
import LeanTrominoes.SAT.Planar.FiniteCrossingRanks

/-! # A finite, complete enumeration of vertical crossing heights -/
namespace LeanTrominoes.PeriodicGridDrawing
open PeriodicOrthocrossing

def nineEdgeCopies {Vertex : Type*} (graph : PeriodicGraph Vertex) : List (Nat × Cell) :=
  graph.edges.zipIdx.flatMap (fun tagged => neighborTranslations.map (fun cell => (tagged.2,cell)))

def verticalCrossingCopies {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing) (line : Int) : List (Nat × Cell) :=
  (nineEdgeCopies graph).filter (fun key => decide
    ((drawing.liftedStraightSegment key.1 key.2).CrossesVerticalLine line ∧
      0 ≤ (drawing.liftedStraightSegment key.1 key.2).rationalLineHeight line ∧
      (drawing.liftedStraightSegment key.1 key.2).rationalLineHeight line < (drawing.gridSize : ℚ)))

def verticalCrossingHeights {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing) (line : Int) : Finset ℚ :=
  ((verticalCrossingCopies graph drawing line).map
    (fun key => (drawing.liftedStraightSegment key.1 key.2).rationalLineHeight line)).toFinset

theorem nineEdgeCopies_length {Vertex : Type*} (graph : PeriodicGraph Vertex) :
    (nineEdgeCopies graph).length = 9*graph.edges.length := by
  unfold nineEdgeCopies
  rw [List.length_flatMap]
  simp only [List.length_map,show neighborTranslations.length = 9 by decide +kernel]
  simp [List.length_zipIdx,Nat.mul_comm]

theorem mem_nineEdgeCopies {Vertex : Type*} {graph : PeriodicGraph Vertex} {key : Nat × Cell} :
    key ∈ nineEdgeCopies graph ↔ ∃ tagged ∈ graph.edges.zipIdx, tagged.2 = key.1 ∧ key.2 ∈ neighborTranslations := by
  simp only [nineEdgeCopies,List.mem_flatMap,List.mem_map]
  constructor
  · rintro ⟨tagged,member,cell,cellMember,equal⟩
    have indices := congrArg Prod.fst equal
    have cells := congrArg Prod.snd equal
    exact ⟨tagged,member,indices,by simpa only [← cells] using cellMember⟩
  · rintro ⟨tagged,member,index,cellMember⟩
    exact ⟨tagged,member,key.2,cellMember,Prod.ext index rfl⟩

theorem verticalCrossingHeights_card_bound {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (compatible : drawing.IsCompatible graph)
    (degree : graph.DegreeAtMost 4) (line : Int) :
    (verticalCrossingHeights graph drawing line).card ≤ 18*drawing.gridSize^2 := by
  have finite := List.toFinset_card_le
    ((verticalCrossingCopies graph drawing line).map
      (fun key => (drawing.liftedStraightSegment key.1 key.2).rationalLineHeight line))
  have filtered := List.length_filter_le (fun key => decide
    ((drawing.liftedStraightSegment key.1 key.2).CrossesVerticalLine line ∧
      0 ≤ (drawing.liftedStraightSegment key.1 key.2).rationalLineHeight line ∧
      (drawing.liftedStraightSegment key.1 key.2).rationalLineHeight line < (drawing.gridSize : ℚ))) (nineEdgeCopies graph)
  have copies := nineEdgeCopies_length graph
  have bound := nine_copy_edge_count_bound compatible degree
  unfold verticalCrossingHeights verticalCrossingCopies
  simp only [verticalCrossingCopies,List.length_map] at finite
  omega

theorem verticalCrossingCopies_complete {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (compatible : drawing.IsCompatible graph)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (straight : (drawing.edgeRoute tagged.2).length = 2) (edgeLocal : tagged.1.span ≤ 1)
    {line : Int} (lineBounds : 0 ≤ line ∧ line ≤ drawing.gridSize) (cell : Cell)
    (crosses : (drawing.liftedStraightSegment tagged.2 cell).CrossesVerticalLine line)
    (heightBounds : 0 ≤ (drawing.liftedStraightSegment tagged.2 cell).rationalLineHeight line ∧
      (drawing.liftedStraightSegment tagged.2 cell).rationalLineHeight line < (drawing.gridSize : ℚ)) :
    (tagged.2,cell) ∈ verticalCrossingCopies graph drawing line := by
  have segmentContains := GridSegment.rationalLineHeight_realContains crosses
  have routeContains := (realEdgeRoute_straight_image drawing tagged.2 cell straight _).mpr segmentContains
  have pointBounds : 0 ≤ (line : ℝ) ∧ (line : ℝ) ≤ drawing.gridSize ∧
      0 ≤ ((drawing.liftedStraightSegment tagged.2 cell).rationalLineHeight line : ℝ) ∧
      ((drawing.liftedStraightSegment tagged.2 cell).rationalLineHeight line : ℝ) ≤ drawing.gridSize := by
    exact ⟨by exact_mod_cast lineBounds.1,by exact_mod_cast lineBounds.2,
      by exact_mod_cast heightBounds.1,by exact_mod_cast heightBounds.2.le⟩
  have neighbor := straight_realEdgeRoute_copy_window compatible member straight edgeLocal cell pointBounds routeContains
  apply List.mem_filter.mpr
  exact ⟨mem_nineEdgeCopies.mpr ⟨tagged,member,rfl,neighbor⟩,by simpa using And.intro crosses heightBounds⟩

end LeanTrominoes.PeriodicGridDrawing
