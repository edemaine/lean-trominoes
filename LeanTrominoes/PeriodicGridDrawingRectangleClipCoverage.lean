/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRectangleContactCoverage
import LeanTrominoes.PeriodicGridDrawingRectangleInputMatching

/-! # Every parent with a rectangle port has exactly two retained ports -/
namespace LeanTrominoes.PeriodicGridDrawing
open RationalAffineBoundary

theorem rectangle_affine_cut_height {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (column : Nat) (parent : Nat × Cell) (right : Bool) :
    rectangleAffineBase graph drawing column parent+(drawing.liftedStraightSegment parent.1 parent.2).rationalSlope*
      (if right then 1-2*columnPerturbation graph drawing else 0) =
      (drawing.liftedStraightSegment parent.1 parent.2).rationalHeightAt
        ((column : ℚ)+(if right then 1-columnPerturbation graph drawing else columnPerturbation graph drawing))+seamPerturbation graph drawing := by
  rw [rectangle_affine_height]
  congr 2
  cases right <;> simp <;> ring

theorem rectangle_affine_corners_avoided {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx) (edgeLocal : tagged.1.span ≤ 1)
    (cell : Cell) (column : Nat) (columnBound : column < drawing.gridSize) (right top : Bool)
    (spans : (drawing.liftedStraightSegment tagged.2 cell).SpansUnitColumn column) :
    rectangleAffineBase graph drawing column (tagged.2,cell)+(drawing.liftedStraightSegment tagged.2 cell).rationalSlope*
      (if right then 1-2*columnPerturbation graph drawing else 0) ≠ (if top then (drawing.gridSize : ℚ) else 0) := by
  have away := virtual_column_cut_height_avoids_row_seams planar straight member edgeLocal cell column columnBound right top spans
  rw [rectangle_affine_cut_height]
  intro equal
  apply away
  cases top <;> simp only [Bool.false_eq_true,if_false,if_true,mul_zero,mul_one] at equal ⊢ <;> linarith

theorem rectanglePort_rationalPoint_eq_of_virtualPort_eq {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing) (column : Nat) {first last : RectanglePortKey Vertex}
    (equal : first.virtualPort graph drawing column = last.virtualPort graph drawing column) :
    first.rationalPoint graph drawing column = last.rationalPoint graph drawing column := by
  have sides := congrArg RealRectangleBoundary.Port.side equal
  rw [rectanglePort_virtual_side,rectanglePort_virtual_side] at sides
  have coordinates := congrArg RealRectangleBoundary.Port.coordinate equal
  rw [rectanglePort_virtual_coordinate,rectanglePort_virtual_coordinate] at coordinates
  have rationalCoordinates : first.rationalCoordinate graph drawing column = last.rationalCoordinate graph drawing column := by exact_mod_cast coordinates
  unfold RectanglePortKey.rationalPoint
  rw [sides,rationalCoordinates]

theorem rectanglePort_parent_two_contacts {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (column : Nat) (columnBound : column < drawing.gridSize) {key : RectanglePortKey Vertex} (valid : key.Valid graph drawing column) :
    ∃ first last : RectanglePortKey Vertex, first.Valid graph drawing column ∧ last.Valid graph drawing column ∧
      first.parentKey = key.parentKey ∧ last.parentKey = key.parentKey ∧
      first.virtualPort graph drawing column ≠ last.virtualPort graph drawing column := by
  obtain ⟨tagged,member,index⟩ := rectanglePort_parent_tagged valid
  have edgeLocal := graphLocal _ (List.fst_mem_of_mem_zipIdx member)
  have spans := rectanglePort_parent_spans_unit_column planar graphLocal straight column valid
  have contact := rectanglePort_rational_contact planar graphLocal straight column valid
  rw [← index] at spans
  have parentEq : key.parentKey = (tagged.2,key.parentKey.2) := Prod.ext index.symm rfl
  rw [parentEq] at contact
  have corner := rectangle_affine_corners_avoided planar straight member edgeLocal key.parentKey.2 column columnBound
  have widthPositive := virtualSlabWidth_positive (columnPerturbation_le_cutMargin planar straight)
  have heightPositive : (0 : ℚ) < drawing.gridSize := by exact_mod_cast Nat.zero_lt_succ drawing.gridSizePred
  obtain ⟨firstPoint,lastPoint,firstContact,lastContact,different⟩ := two_distinct_contacts widthPositive heightPositive
    (by simpa using corner false false spans) (by simpa using corner false true spans)
    (by simpa using corner true false spans) (by simpa using corner true true spans) contact
  obtain ⟨first,firstValid,firstParent,firstPointEq⟩ := rational_rectangle_contact_retained planar straight member edgeLocal
    key.parentKey.2 column columnBound firstPoint spans firstContact
  obtain ⟨last,lastValid,lastParent,lastPointEq⟩ := rational_rectangle_contact_retained planar straight member edgeLocal
    key.parentKey.2 column columnBound lastPoint spans lastContact
  refine ⟨first,last,firstValid,lastValid,?_,?_,?_⟩
  · simpa only [index,Prod.eta] using firstParent
  · simpa only [index,Prod.eta] using lastParent
  · intro equal
    apply different
    rw [← firstPointEq,← lastPointEq]
    exact rectanglePort_rationalPoint_eq_of_virtualPort_eq graph drawing column equal

theorem rectangleParentPorts_length_eq_two_of_port {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (column : Nat) (columnBound : column < drawing.gridSize) {key : RectanglePortKey Vertex} (valid : key.Valid graph drawing column) :
    (rectangleParentPorts graph drawing column key.parentKey).length = 2 := by
  obtain ⟨first,last,firstValid,lastValid,firstParent,lastParent,different⟩ := rectanglePort_parent_two_contacts planar graphLocal straight column columnBound valid
  obtain ⟨firstRepresentative,firstAt,firstEqual⟩ := rectangleParentPorts_cover graph drawing column key.parentKey firstValid firstParent
  obtain ⟨lastRepresentative,lastAt,lastEqual⟩ := rectangleParentPorts_cover graph drawing column key.parentKey lastValid lastParent
  have representativesDifferent : firstRepresentative ≠ lastRepresentative := by
    intro equal
    apply different
    rw [← firstEqual,← lastEqual,equal]
  have lower : 2 ≤ (rectangleParentPorts graph drawing column key.parentKey).length := by
    generalize portsEq : rectangleParentPorts graph drawing column key.parentKey = ports at firstAt lastAt ⊢
    cases ports with
    | nil => simp at firstAt
    | cons head tail =>
      cases tail with
      | nil =>
        simp only [List.mem_singleton] at firstAt lastAt
        exact (representativesDifferent (firstAt.trans lastAt.symm)).elim
      | cons second tail => simp
  have upper := rectangleParentPorts_length_le_two planar graphLocal straight column key.parentKey
  omega

theorem rectangleParentChord_exists_of_port {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (column : Nat) (columnBound : column < drawing.gridSize) {key : RectanglePortKey Vertex} (valid : key.Valid graph drawing column) :
    ∃ first last : RectanglePortKey Vertex, rectangleParentChord graph drawing column key.parentKey = some (first,last) := by
  obtain ⟨first,last,ports⟩ := List.length_eq_two.mp (rectangleParentPorts_length_eq_two_of_port planar graphLocal straight column columnBound valid)
  exact ⟨first,last,(rectangleParentChord_some_iff graph drawing column key.parentKey first last).mpr ports⟩

end LeanTrominoes.PeriodicGridDrawing
