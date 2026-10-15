/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingRationalPortOrder
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingRectanglePortParents

/-! # Computable complete lists of the valid rectangle boundary ports -/
namespace LeanTrominoes.PeriodicGridDrawing

instance columnPortKeyValidDecidable {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex)
    (drawing : PeriodicGridDrawing) (column : Int) (right : Bool) (key : ColumnPortKey Vertex) :
    Decidable (key.Valid graph drawing column right) := by
  cases key <;> unfold ColumnPortKey.Valid <;> infer_instance

instance rectanglePortKeyValidDecidable {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex)
    (drawing : PeriodicGridDrawing) (column : Nat) (key : RectanglePortKey Vertex) :
    Decidable (key.Valid graph drawing column) := by
  cases key <;> unfold RectanglePortKey.Valid <;> infer_instance

def columnPortCandidates {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (column : Int) (right : Bool) : List (ColumnPortKey Vertex) :=
  ((verticalCrossingCopies graph drawing column).map ColumnPortKey.crossing) ++
    (graph.edges.zipIdx.flatMap fun tagged => [ColumnPortKey.incidence tagged false,ColumnPortKey.incidence tagged true]).filter
      (fun key => decide (key.Valid graph drawing column right))

theorem mem_columnPortCandidates {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (column : Int) (right : Bool) (key : ColumnPortKey Vertex) :
    key ∈ columnPortCandidates graph drawing column right ↔ key.Valid graph drawing column right := by
  constructor
  · intro member
    unfold columnPortCandidates at member
    rcases List.mem_append.mp member with crossed | incident
    · obtain ⟨crossingKey,crossingAt,rfl⟩ := List.mem_map.mp crossed
      exact crossingAt
    · exact of_decide_eq_true (List.mem_filter.mp incident).2
  · intro valid
    unfold columnPortCandidates
    apply List.mem_append.mpr
    cases key with
    | crossing key => exact Or.inl (List.mem_map.mpr ⟨key,valid,rfl⟩)
    | incidence tagged target =>
      right
      apply List.mem_filter.mpr
      refine ⟨List.mem_flatMap.mpr ⟨tagged,valid.1,?_⟩,by simpa using valid⟩
      cases target <;> simp

def rectanglePortCandidates {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (column : Nat) : List (RectanglePortKey Vertex) :=
  ([false,true].flatMap fun right => (columnPortCandidates graph drawing ((column+if right then 1 else 0 : Nat) : Int) right).map
    (RectanglePortKey.vertical right)) ++
  ([false,true].flatMap fun top => ((seamCrossingCopies graph drawing 0).filter
    (fun key => decide (seamAssignedSlab graph drawing key = column))).map (RectanglePortKey.horizontal top))

theorem mem_rectanglePortCandidates {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (column : Nat) (key : RectanglePortKey Vertex) :
    key ∈ rectanglePortCandidates graph drawing column ↔ key.Valid graph drawing column := by
  constructor
  · intro member
    unfold rectanglePortCandidates at member
    rcases List.mem_append.mp member with vertical | horizontal
    · obtain ⟨right,_,mapped⟩ := List.mem_flatMap.mp vertical
      obtain ⟨port,portAt,rfl⟩ := List.mem_map.mp mapped
      exact (mem_columnPortCandidates graph drawing _ right port).mp portAt
    · obtain ⟨top,_,mapped⟩ := List.mem_flatMap.mp horizontal
      obtain ⟨seamKey,seamAt,rfl⟩ := List.mem_map.mp mapped
      have data := List.mem_filter.mp seamAt
      exact ⟨data.1,of_decide_eq_true data.2⟩
  · intro valid
    unfold rectanglePortCandidates
    apply List.mem_append.mpr
    cases key with
    | vertical right key =>
      left
      exact List.mem_flatMap.mpr ⟨right,by cases right <;> simp,List.mem_map.mpr
        ⟨key,(mem_columnPortCandidates graph drawing _ right key).mpr valid,rfl⟩⟩
    | horizontal top key =>
      right
      exact List.mem_flatMap.mpr ⟨top,by cases top <;> simp,List.mem_map.mpr
        ⟨key,List.mem_filter.mpr ⟨valid.1,by simpa using valid.2⟩,rfl⟩⟩

def rectangleParentPortCandidates {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (column : Nat) (parent : Nat × Cell) : List (RectanglePortKey Vertex) :=
  (rectanglePortCandidates graph drawing column).filter fun key => decide (key.parentKey = parent)

theorem mem_rectangleParentPortCandidates {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (column : Nat) (parent : Nat × Cell) (key : RectanglePortKey Vertex) :
    key ∈ rectangleParentPortCandidates graph drawing column parent ↔ key.Valid graph drawing column ∧ key.parentKey = parent := by
  simp only [rectangleParentPortCandidates,List.mem_filter,mem_rectanglePortCandidates,decide_eq_true_eq]

end LeanTrominoes.PeriodicGridDrawing
