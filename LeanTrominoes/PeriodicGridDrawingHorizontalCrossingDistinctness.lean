/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingHorizontalCrossingEnumeration
import LeanTrominoes.PeriodicGridDrawingVerticalCrossingDistinctness

/-! # Exact horizontal crossing coordinates identify their edge occurrence -/
namespace LeanTrominoes.PeriodicGridDrawing

theorem horizontalCrossingCopies_abscissa_injective {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2) (line : Int)
    {first second : Nat × Cell} (firstMember : first ∈ horizontalCrossingCopies graph drawing line)
    (secondMember : second ∈ horizontalCrossingCopies graph drawing line)
    (equal : (drawing.liftedStraightSegment first.1 first.2).rationalLineAbscissa line =
      (drawing.liftedStraightSegment second.1 second.2).rationalLineAbscissa line) : first = second := by
  by_contra different
  obtain ⟨firstTagged,firstAt,firstIndex,_⟩ := mem_nineEdgeCopies.mp (List.mem_filter.mp firstMember).1
  obtain ⟨secondTagged,secondAt,secondIndex,_⟩ := mem_nineEdgeCopies.mp (List.mem_filter.mp secondMember).1
  have firstValid : first.1 < drawing.edgeRoutes.length := by
    rw [planar.1.1.2.2.1,← firstIndex]
    exact List.snd_lt_of_mem_zipIdx firstAt
  have secondValid : second.1 < drawing.edgeRoutes.length := by
    rw [planar.1.1.2.2.1,← secondIndex]
    exact List.snd_lt_of_mem_zipIdx secondAt
  have firstStraight : (drawing.edgeRoute first.1).length = 2 := by rw [← firstIndex]; exact straight _ firstAt
  have secondStraight : (drawing.edgeRoute second.1).length = 2 := by rw [← secondIndex]; exact straight _ secondAt
  have firstCrosses : (drawing.liftedStraightSegment first.1 first.2).CrossesHorizontalLine line := by
    have data := (List.mem_filter.mp firstMember).2
    simp only [decide_eq_true_eq] at data
    exact data.1
  have secondCrosses : (drawing.liftedStraightSegment second.1 second.2).CrossesHorizontalLine line := by
    have data := (List.mem_filter.mp secondMember).2
    simp only [decide_eq_true_eq] at data
    exact data.1
  exact horizontal_crossing_abscissae_ne planar.2 firstValid secondValid firstStraight secondStraight first.2 second.2
    (by simpa only [Prod.eta] using different) firstCrosses secondCrosses equal

theorem horizontalCrossingCopies_nodup {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing) (line : Int) :
    (horizontalCrossingCopies graph drawing line).Nodup := (nineEdgeCopies_nodup graph).filter _

end LeanTrominoes.PeriodicGridDrawing
