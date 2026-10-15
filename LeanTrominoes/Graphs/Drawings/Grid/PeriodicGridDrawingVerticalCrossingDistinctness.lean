/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingVerticalCrossingEnumeration
import Mathlib.Data.List.Sigma

/-! # Crossing-table keys and their rational heights are both duplicate-free -/
namespace LeanTrominoes.PeriodicGridDrawing
open PeriodicOrthocrossing

theorem nineEdgeCopies_nodup {Vertex : Type*} (graph : PeriodicGraph Vertex) : (nineEdgeCopies graph).Nodup := by
  have product : nineEdgeCopies graph = (graph.edges.zipIdx.map Prod.snd).product neighborTranslations := by
    simp only [nineEdgeCopies,List.product,List.flatMap_map,Function.comp_def]
  rw [product]
  exact (List.nodup_zipIdx_map_snd _).product (by decide +kernel)

theorem verticalCrossingCopies_nodup {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing) (line : Int) :
    (verticalCrossingCopies graph drawing line).Nodup := (nineEdgeCopies_nodup graph).filter _

theorem verticalCrossingCopies_height_injective {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2) (line : Int)
    {first second : Nat × Cell} (firstMember : first ∈ verticalCrossingCopies graph drawing line)
    (secondMember : second ∈ verticalCrossingCopies graph drawing line)
    (equal : (drawing.liftedStraightSegment first.1 first.2).rationalLineHeight line =
      (drawing.liftedStraightSegment second.1 second.2).rationalLineHeight line) : first = second := by
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
  have firstCrosses : (drawing.liftedStraightSegment first.1 first.2).CrossesVerticalLine line := by
    have data := (List.mem_filter.mp firstMember).2
    simp only [decide_eq_true_eq] at data
    exact data.1
  have secondCrosses : (drawing.liftedStraightSegment second.1 second.2).CrossesVerticalLine line := by
    have data := (List.mem_filter.mp secondMember).2
    simp only [decide_eq_true_eq] at data
    exact data.1
  exact vertical_crossing_heights_ne planar.2 firstValid secondValid firstStraight secondStraight first.2 second.2
    (by simpa only [Prod.eta] using different) firstCrosses secondCrosses equal

theorem verticalCrossingHeights_nodup {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2) (line : Int) :
    ((verticalCrossingCopies graph drawing line).map
      (fun key => (drawing.liftedStraightSegment key.1 key.2).rationalLineHeight line)).Nodup :=
  List.Nodup.map_on (fun _ firstMember _ secondMember equal =>
    verticalCrossingCopies_height_injective planar straight line firstMember secondMember equal)
      (verticalCrossingCopies_nodup graph drawing line)

theorem verticalCrossingHeights_card_eq {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2) (line : Int) :
    (verticalCrossingHeights graph drawing line).card = (verticalCrossingCopies graph drawing line).length := by
  unfold verticalCrossingHeights
  rw [List.toFinset_card_of_nodup (verticalCrossingHeights_nodup planar straight line),List.length_map]

end LeanTrominoes.PeriodicGridDrawing
