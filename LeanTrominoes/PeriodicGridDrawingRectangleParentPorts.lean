/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRectanglePortEnumeration
import LeanTrominoes.PeriodicGridDrawingRectangleChordGeometry
import LeanTrominoes.FiniteKeyDedup

/-! # Each edge occurrence has at most two computably ordered rectangle ports -/
namespace LeanTrominoes.PeriodicGridDrawing

def rectangleParentPorts {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (column : Nat) (parent : Nat × Cell) : List (RectanglePortKey Vertex) :=
  (FiniteKeyDedup.retain (RectanglePortKey.rationalCode graph drawing column)
    (rectangleParentPortCandidates graph drawing column parent)).mergeSort
      (fun first last => decide (first.rationalCode graph drawing column ≤ last.rationalCode graph drawing column))

theorem rectangleParentPorts_valid {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (column : Nat) (parent : Nat × Cell) {key : RectanglePortKey Vertex}
    (member : key ∈ rectangleParentPorts graph drawing column parent) : key.Valid graph drawing column ∧ key.parentKey = parent := by
  have retained := (List.mergeSort_perm _ _).mem_iff.mp member
  have candidate := FiniteKeyDedup.subset _ _ retained
  exact (mem_rectangleParentPortCandidates graph drawing column parent key).mp candidate

theorem rectangleParentPorts_ordered {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (column : Nat) (parent : Nat × Cell) :
    (rectangleParentPorts graph drawing column parent).Pairwise
      (fun first last => (first.virtualPort graph drawing column).Before (last.virtualPort graph drawing column)) := by
  let code := RectanglePortKey.rationalCode graph drawing column
  let candidates := rectangleParentPortCandidates graph drawing column parent
  let retained := FiniteKeyDedup.retain code candidates
  have weak := List.pairwise_mergeSort
    (le := fun first last : RectanglePortKey Vertex => decide (code first ≤ code last))
    (by intro first middle last fm ml; simp only [decide_eq_true_eq] at *; exact le_trans fm ml)
    (by intro first last; simp only [Bool.or_eq_true,decide_eq_true_eq]; exact le_total _ _) retained
  have nodup := ((List.mergeSort_perm retained (fun first last => decide (code first ≤ code last))).map code).nodup_iff.mpr
    (FiniteKeyDedup.values_nodup code candidates)
  change ((retained.mergeSort (fun first last => decide (code first ≤ code last))).map code).Pairwise (fun first last => first ≠ last) at nodup
  have distinct : (rectangleParentPorts graph drawing column parent).Pairwise (fun first last => code first ≠ code last) := by
    simpa only [List.pairwise_map,rectangleParentPorts,code,retained,candidates] using nodup
  have weakOrder : (rectangleParentPorts graph drawing column parent).Pairwise (fun first last => code first ≤ code last) := by
    simpa only [decide_eq_true_eq,rectangleParentPorts,code,retained,candidates] using weak
  apply (weakOrder.and distinct).imp
  intro first last data
  exact (rectanglePort_virtual_before_iff graph drawing column first last).mpr (lt_of_le_of_ne data.1 data.2)

theorem rectanglePort_eq_of_rationalCode_eq {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (column : Nat) {first last : RectanglePortKey Vertex}
    (equal : first.rationalCode graph drawing column = last.rationalCode graph drawing column) :
    first.virtualPort graph drawing column = last.virtualPort graph drawing column := by
  by_contra different
  have codesDifferent : (first.virtualPort graph drawing column).clockwiseCode ≠ (last.virtualPort graph drawing column).clockwiseCode :=
    fun same => different (RealRectangleBoundary.Port.clockwiseCode_injective same)
  rcases lt_or_gt_of_ne codesDifferent with ordered | ordered
  · have rationalOrder := (rectanglePort_virtual_before_iff graph drawing column first last).mp ordered
    rw [equal] at rationalOrder
    exact lt_irrefl _ rationalOrder
  · have rationalOrder := (rectanglePort_virtual_before_iff graph drawing column last first).mp ordered
    rw [equal] at rationalOrder
    exact lt_irrefl _ rationalOrder

theorem rectangleParentPorts_cover {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (column : Nat) (parent : Nat × Cell) {key : RectanglePortKey Vertex}
    (valid : key.Valid graph drawing column) (sameParent : key.parentKey = parent) :
    ∃ representative ∈ rectangleParentPorts graph drawing column parent,
      representative.virtualPort graph drawing column = key.virtualPort graph drawing column := by
  have member := (mem_rectangleParentPortCandidates graph drawing column parent key).mpr ⟨valid,sameParent⟩
  obtain ⟨representative,retained,equal⟩ := FiniteKeyDedup.covers_values (RectanglePortKey.rationalCode graph drawing column) member
  exact ⟨representative,(List.mergeSort_perm _ _).mem_iff.mpr retained,rectanglePort_eq_of_rationalCode_eq graph drawing column equal⟩

theorem rectangleParentPorts_length_le_two {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (column : Nat) (parent : Nat × Cell) : (rectangleParentPorts graph drawing column parent).length ≤ 2 := by
  have widthPositive : (0 : ℝ) < ((1-2*columnPerturbation graph drawing : ℚ) : ℝ) := by
    exact_mod_cast virtualSlabWidth_positive (columnPerturbation_le_cutMargin planar straight)
  have heightPositive : (0 : ℝ) < drawing.gridSize := by
    have positive : 0 < drawing.gridSize := by unfold PeriodicGridDrawing.gridSize; omega
    exact_mod_cast positive
  have bound := RealRectangleBoundary.ordered_boundary_ports_length_le_two
    (segment := drawing.liftedStraightSegment parent.1 parent.2) widthPositive heightPositive
    ((rectangleParentPorts_ordered graph drawing column parent).map (fun (key : RectanglePortKey Vertex) => key.virtualPort graph drawing column) (fun _ _ ordered => ordered))
    (fun port member => by
      obtain ⟨key,keyAt,rfl⟩ := List.mem_map.mp member
      exact rectanglePort_virtual_inside planar graphLocal straight column (rectangleParentPorts_valid graph drawing column parent keyAt).1)
    (fun port member => by
      obtain ⟨key,keyAt,rfl⟩ := List.mem_map.mp member
      have data := rectangleParentPorts_valid graph drawing column parent keyAt
      have contact := rectanglePort_parent_realInteriorContains planar straight column data.1
      rw [data.2] at contact
      exact GridSegment.realInteriorContains_implies_realContains contact)
    (fun first firstAt last lastAt sameSide => by
      obtain ⟨firstKey,firstMember,rfl⟩ := List.mem_map.mp firstAt
      obtain ⟨lastKey,lastMember,rfl⟩ := List.mem_map.mp lastAt
      have firstData := rectangleParentPorts_valid graph drawing column parent firstMember
      have lastData := rectangleParentPorts_valid graph drawing column parent lastMember
      exact rectanglePort_same_parent_unique_side planar straight column firstData.1 lastData.1
        (firstData.2.trans lastData.2.symm) sameSide)
  simpa only [List.length_map] using bound

end LeanTrominoes.PeriodicGridDrawing
