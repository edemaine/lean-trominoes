/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingVertexCoverage
import Mathlib.Tactic

/-! # Distinct vertex occurrences have distinct lifted coordinates -/
namespace LeanTrominoes.PeriodicGridDrawing

theorem fundamental_position_periodic_eq {drawing : PeriodicGridDrawing} {first second firstCell secondCell : Cell}
    (fb : drawing.PositionInFundamentalSquare first) (sb : drawing.PositionInFundamentalSquare second)
    (equal : Cell.add first (drawing.periodTranslation firstCell) = Cell.add second (drawing.periodTranslation secondCell)) :
    first = second ∧ firstCell = secondCell := by
  have hx := congrArg Prod.fst equal
  have hy := congrArg Prod.snd equal
  simp only [Cell.add,periodTranslation,Cell.scale] at hx hy
  have xmod := congrArg (fun x : Int => x % drawing.gridSize) hx
  have ymod := congrArg (fun x : Int => x % drawing.gridSize) hy
  simp only [Int.add_mul_emod_self_left,Int.emod_eq_of_lt fb.1.le fb.2.1,
    Int.emod_eq_of_lt sb.1.le sb.2.1] at xmod
  simp only [Int.add_mul_emod_self_left,Int.emod_eq_of_lt fb.2.2.1.le fb.2.2.2,
    Int.emod_eq_of_lt sb.2.2.1.le sb.2.2.2] at ymod
  have positions := Prod.ext xmod ymod
  refine ⟨positions,?_⟩
  have positive : (0 : Int) < drawing.gridSize := by
    exact_mod_cast Nat.zero_lt_succ drawing.gridSizePred
  have nonzero := ne_of_gt positive
  apply Prod.ext
  · exact mul_left_cancel₀ nonzero (by omega : (drawing.gridSize : Int)*firstCell.1 = drawing.gridSize*secondCell.1)
  · exact mul_left_cancel₀ nonzero (by omega : (drawing.gridSize : Int)*firstCell.2 = drawing.gridSize*secondCell.2)

theorem IsCompatible.lifted_vertex_eq {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (valid : drawing.IsCompatible graph)
    {first second : Vertex} (fm : first ∈ graph.vertices) (sm : second ∈ graph.vertices)
    {firstCell secondCell : Cell}
    (equal : Cell.add (drawing.vertexPosition graph first) (drawing.periodTranslation firstCell) =
      Cell.add (drawing.vertexPosition graph second) (drawing.periodTranslation secondCell)) :
    first = second ∧ firstCell = secondCell := by
  have coordinates := fundamental_position_periodic_eq
    (valid.2.2.2.2.1 _ (valid.vertexPosition_mem fm))
    (valid.2.2.2.2.1 _ (valid.vertexPosition_mem sm)) equal
  exact ⟨valid.vertexPosition_injective_on fm sm coordinates.1,coordinates.2⟩

end LeanTrominoes.PeriodicGridDrawing
