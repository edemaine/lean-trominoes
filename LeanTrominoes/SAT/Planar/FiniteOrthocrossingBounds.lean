/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Orthogonal.Bounds.PeriodicOrthocrossingBounds

/-! # Zero-offset graphs have routes inside one fundamental square -/
namespace LeanTrominoes.PeriodicOrthocrossing

theorem classifiedSegment_endpoints_inFundamental_of_zero
    {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed) (degree : graph.DegreeAtMost 3)
    {edge : PeriodicEdge Vertex} {edgeIndex : Nat}
    (edgeMem : (edge,edgeIndex)∈graph.edges.zipIdx) (zero : edge.offset=(0,0))
    {classified : ClassifiedSegment Vertex}
    (member : classified∈classifiedRouteSegments graph edge edgeIndex) :
    InFundamentalDrawingSquare graph classified.segment.start ∧
      InFundamentalDrawingSquare graph classified.segment.finish := by
  have endpoints := wellFormed.2 edge (List.fst_mem_of_mem_zipIdx edgeMem)
  have sourceVertex := vertexX_bounds endpoints.1
  have targetVertex := vertexX_bounds endpoints.2
  have sourcePortBounds := portX_bounds wellFormed degree (sourcePort_mem_allPorts graph edgeMem)
  have targetPortBounds := portX_bounds wellFormed degree (targetPort_mem_allPorts graph edgeMem)
  have tracks := edgeTrack_bounds graph edgeMem
  dsimp only at sourcePortBounds targetPortBounds tracks
  have sourceAll : ∀ item∈classifiedSourceFanout graph edge edgeIndex,
      InFundamentalDrawingSquare graph item.segment.start ∧
        InFundamentalDrawingSquare graph item.segment.finish := by
    simp [classifiedSourceFanout,InFundamentalDrawingSquare]
    split <;> simp_all <;> omega
  have coreAll : ∀ item∈classifiedEdgeCore graph edge edgeIndex,
      InFundamentalDrawingSquare graph item.segment.start ∧
        InFundamentalDrawingSquare graph item.segment.finish := by
    simp [classifiedEdgeCore,zero,InFundamentalDrawingSquare,Cell.add,Cell.scale]
    omega
  have targetAll : ∀ item∈classifiedTargetFanout graph edge edgeIndex,
      InFundamentalDrawingSquare graph item.segment.start ∧
        InFundamentalDrawingSquare graph item.segment.finish := by
    simp [classifiedTargetFanout,zero,InFundamentalDrawingSquare,Cell.add,Cell.scale]
    split <;> simp_all <;> omega
  rcases List.mem_append.mp member with first|last
  · exact (List.mem_append.mp first).elim (sourceAll classified) (coreAll classified)
  · exact targetAll classified last

theorem drawing_indexedSegment_endpoints_inFundamental_of_zero
    {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed) (degree : graph.DegreeAtMost 3)
    (zero : ∀ edge∈graph.edges, edge.offset=(0,0))
    {indexed : IndexedGridSegment} (member : indexed∈(drawing graph).indexedSegments) :
    InFundamentalDrawingSquare graph indexed.segment.start ∧
      InFundamentalDrawingSquare graph indexed.segment.finish := by
  obtain ⟨route,hr,classified,hc,rfl⟩ := exists_classifiedSegment_of_drawing_mem member
  have edgeMem := List.fst_mem_of_mem_zipIdx hr
  exact classifiedSegment_endpoints_inFundamental_of_zero wellFormed degree edgeMem
    (zero _ (List.fst_mem_of_mem_zipIdx edgeMem)) (List.fst_mem_of_mem_zipIdx hc)

private theorem between_shift_zero {period first last shift point : Int}
    (positive : 0<period) (firstBounds : 0≤first ∧ first<period)
    (lastBounds : 0≤last ∧ last<period) (pointBounds : 0≤point ∧ point<period)
    (between : GridSegment.Between (first+period*shift) (last+period*shift) point) :
    shift=0 := by
  have notNegative : ¬shift<0 := by
    intro negative
    have product := mul_le_mul_of_nonneg_left (show shift≤-1 by omega) (le_of_lt positive)
    rcases between with h|h <;> nlinarith
  have notPositive : ¬0<shift := by
    intro positiveShift
    have product := mul_le_mul_of_nonneg_left (show 1≤shift by omega) (le_of_lt positive)
    rcases between with h|h <;> nlinarith
  omega

/-- A route from a zero-offset graph can meet the canonical square only in
its zero translate. This rules out interactions between neighboring copies. -/
theorem drawing_occurrence_translate_zero
    {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed) (degree : graph.DegreeAtMost 3)
    (zero : ∀ edge∈graph.edges, edge.offset=(0,0))
    {indexed : IndexedGridSegment} (member : indexed∈(drawing graph).indexedSegments)
    {translate point : Cell} (fundamental : InFundamentalDrawingSquare graph point)
    (contains : (indexed.segment.translate ((drawing graph).periodTranslation translate)).InteriorContains point) :
    translate=(0,0) := by
  have bounds := drawing_indexedSegment_endpoints_inFundamental_of_zero wellFormed degree zero member
  have positive : (0:Int)<drawingGridSize graph := by exact_mod_cast drawingGridSize_pos graph
  have closed : (indexed.segment.translate ((drawing graph).periodTranslation translate)).Contains point := by
    rcases contains with ⟨h,eq,between⟩|⟨h,eq,between⟩
    · exact Or.inl ⟨h,eq,between.elim (fun h => Or.inl ⟨le_of_lt h.1,le_of_lt h.2⟩)
        (fun h => Or.inr ⟨le_of_lt h.1,le_of_lt h.2⟩)⟩
    · exact Or.inr ⟨h,eq,between.elim (fun h => Or.inl ⟨le_of_lt h.1,le_of_lt h.2⟩)
        (fun h => Or.inr ⟨le_of_lt h.1,le_of_lt h.2⟩)⟩
  have rectangular :
      GridSegment.Between (indexed.segment.start.1+drawingGridSize graph*translate.1)
        (indexed.segment.finish.1+drawingGridSize graph*translate.1) point.1 ∧
      GridSegment.Between (indexed.segment.start.2+drawingGridSize graph*translate.2)
        (indexed.segment.finish.2+drawingGridSize graph*translate.2) point.2 := by
    rcases closed with ⟨h,eq,between⟩|⟨h,eq,between⟩
    · simp only [GridSegment.IsHorizontal,GridSegment.translate,Cell.add,
        PeriodicGridDrawing.periodTranslation,drawing_gridSize,Cell.scale] at h eq between
      constructor
      · simpa [add_comm] using between
      · simp only [GridSegment.Between]
        omega
    · simp only [GridSegment.IsVertical,GridSegment.translate,Cell.add,
        PeriodicGridDrawing.periodTranslation,drawing_gridSize,Cell.scale] at h eq between
      constructor
      · simp only [GridSegment.Between]
        omega
      · simpa [add_comm] using between
  exact Prod.ext
    (between_shift_zero positive ⟨bounds.1.1,bounds.1.2.1⟩ ⟨bounds.2.1,bounds.2.2.1⟩
      ⟨fundamental.1,fundamental.2.1⟩ rectangular.1)
    (between_shift_zero positive ⟨bounds.1.2.2.1,bounds.1.2.2.2⟩ ⟨bounds.2.2.2.1,bounds.2.2.2.2⟩
      ⟨fundamental.2.2.1,fundamental.2.2.2⟩ rectangular.2)

end LeanTrominoes.PeriodicOrthocrossing
