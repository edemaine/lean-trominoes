/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.DelimitedDirectionVertexCounts
import LeanTrominoes.UnitRouteEndpointDisplacement
import LeanTrominoes.PrefixSumsGetElem

/-! # Exact coordinates of every vertex reconstructed from unit directions -/
namespace LeanTrominoes.DelimitedDirectionDisplacement

private theorem sum_indicators (direction : AxisDirection) (route : List AxisDirection) :
    (route.map (fun next => if next = direction then 1 else 0)).sum = route.count direction := by
  induction route with
  | nil => rfl
  | cons next route ih =>
      by_cases h : next = direction <;> simp [h, ih, Nat.add_comm]

theorem vertexCounts_getElem (direction : AxisDirection) (route : List AxisDirection)
    (index : Nat) (bound : index ≤ route.length) :
    (vertexCounts direction route)[index]'(by simp; omega) = (route.take index).count direction := by
  unfold vertexCounts
  rw [PrefixSums.starts_getElem _ _ (by simp; omega)]
  rw [List.take_append_of_le_length (by simpa using bound), ← List.map_take]
  exact sum_indicators direction (route.take index)

theorem vertexCounts_eq_range (direction : AxisDirection) (route : List AxisDirection) :
    vertexCounts direction route =
      (List.range (route.length + 1)).map (fun index => (route.take index).count direction) := by
  apply List.ext_getElem
  · simp
  · intro index left right
    simp only [List.getElem_map, List.getElem_range]
    exact vertexCounts_getElem direction route index (by simpa using Nat.le_of_lt_succ (by simpa using left))

/-- Vertex rows retain their parent row and their position within its route. -/
def vertexRows {Index : Type} (rows : List Index) (directions : Index → List AxisDirection) :
    List (Index × Nat) :=
  rows.flatMap (fun row => (List.range ((directions row).length + 1)).map (row, ·))

theorem vertexRows_counts {Index : Type} (rows : List Index)
    (directions : Index → List AxisDirection) (direction : AxisDirection) :
    (rows.map directions).flatMap (vertexCounts direction) =
      (vertexRows rows directions).map (fun row => ((directions row.1).take row.2).count direction) := by
  simp only [List.flatMap_map, vertexCounts_eq_range, vertexRows,
    List.map_flatMap, List.map_map, Function.comp_def]

theorem vertexRows_constant {Index : Type} (rows : List Index)
    (directions : Index → List AxisDirection) (value : Index → Nat) :
    rows.flatMap (fun row => List.replicate ((directions row).length + 1) (value row)) =
      (vertexRows rows directions).map (fun row => value row.1) := by
  simp [vertexRows, List.map_flatMap, List.map_map, Function.comp_def, List.map_const']

/-- The point reached after exactly `index` steps. -/
def vertexPoint (start : Cell) (directions : List AxisDirection) (index : Nat) : Cell :=
  Cell.add start (displacement true (directions.take index), displacement false (directions.take index))

theorem vertexPoint_component (horizontal : Bool) (start : Cell)
    (directions : List AxisDirection) (index : Nat) :
    component horizontal (vertexPoint start directions index) =
      component horizontal start + displacement horizontal (directions.take index) := by
  cases horizontal <;> simp [vertexPoint, component, Cell.add]

private theorem rebuildRoute_getElem (start : Cell) (directions : List AxisDirection)
    (index : Nat) (bound : index ≤ directions.length) :
    (Gadget.rebuildRoute start directions)[index]'(by simp; omega) = vertexPoint start directions index := by
  induction directions generalizing start index with
  | nil =>
      have hi : index = 0 := by simpa using bound
      subst index
      simp [Gadget.rebuildRoute, vertexPoint, displacement, Cell.add]
  | cons direction directions ih =>
      cases index with
      | zero => simp [Gadget.rebuildRoute, vertexPoint, displacement, Cell.add]
      | succ index =>
          simp only [Gadget.rebuildRoute, List.getElem_cons_succ]
          rw [ih _ index (by simpa using bound)]
          apply Prod.ext <;>
            simp [vertexPoint, List.take_succ_cons, displacement, Cell.add, component] <;> omega

/-- Indexed reconstruction preserves the entire ordered point list. -/
theorem rebuildRoute_eq_vertices (start : Cell) (directions : List AxisDirection) :
    Gadget.rebuildRoute start directions =
      (List.range (directions.length + 1)).map (vertexPoint start directions) := by
  apply List.ext_getElem
  · simp
  · intro index left right
    simp only [List.getElem_map, List.getElem_range]
    exact rebuildRoute_getElem start directions index (by simpa using Nat.le_of_lt_succ (by simpa using left))

/-- Unit-step routes, including singletons, are reconstructed without inserting points. -/
theorem unitRoute_eq_vertices (points : List Cell) (start : Cell)
    (head : points.head? = some start) (unitSteps : points.IsChain AxisDirection.IsUnitAxisStep) :
    points = (List.range ((Gadget.unitSubdivisionDirections points).length + 1)).map
      (vertexPoint start (Gadget.unitSubdivisionDirections points)) := by
  cases points with
  | nil => simp at head
  | cons first rest =>
      have h : first = start := Option.some.inj head
      subst first
      rw [Gadget.unitSubdivisionDirections_eq_routeStepDirections_of_unitSteps _ unitSteps,
        ← rebuildRoute_eq_vertices, Gadget.rebuildRoute_routeStepDirections start rest unitSteps]

end LeanTrominoes.DelimitedDirectionDisplacement
