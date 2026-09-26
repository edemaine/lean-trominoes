/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.DelimitedDirectionVertexCompiler

/-! # Successor-step metadata aligned with every reconstructed route vertex -/
noncomputable section
namespace LeanTrominoes.DelimitedDirectionDisplacement
open Computability Turing UnaryColumn

private theorem map_with_end {A B : Type} (items : List A) (f : Option A → B) :
    items.map (fun item => f (some item)) ++ [f none] =
      (List.range (items.length + 1)).map (fun i => f items[i]?) := by
  induction items with
  | nil => simp
  | cons item items ih =>
      simp only [List.map_cons, List.cons_append, List.length_cons]
      rw [List.range_succ_eq_map]
      simp only [List.map_cons, List.getElem?_cons_zero, List.map_map]
      exact congrArg (List.cons (f (some item))) ih

def vertexTokenValue (f : Option AxisDirection → Nat) : Token → Nat
  | .direction direction => f (some direction)
  | .routeEnd => f none

variable {Symbol Index : Type} [Fintype Symbol] [Inhabited Symbol]
    (rows : List Symbol → List Index) (directions : List Symbol → Index → List AxisDirection)
    (routesCompiler : TM2ComputableInPolyTime id id (fun s => words ((rows s).map (directions s))))

def vertexDirectionValueCompiler (f : Option AxisDirection → Nat) :
    Compiler (fun s => vertexRows (rows s) (directions s))
      (fun s row => f (directions s row.1)[row.2]?) := by
  let physical := TM2CompositionMachine.computableInPolyTime routesCompiler
    (FiniteUnaryFieldMap.computableInPolyTime (vertexTokenValue f))
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  simp only [FiniteUnaryFieldMap.values, words, word, List.map_flatMap, List.flatMap_map,
    List.map_append, List.map_cons, List.map_nil, List.map_map, Function.comp_def,
    vertexTokenValue, map_with_end, vertexRows]

private theorem count_take_next (direction : AxisDirection) (route : List AxisDirection) (i : Nat) :
    (route.take (i + 1)).count direction = (route.take i).count direction +
      ((route[i]?).map (fun next => if next = direction then 1 else 0)).getD 0 := by
  by_cases bound : i < route.length
  · rw [List.take_succ_eq_append_getElem bound]
    simp only [List.count_append, List.count_singleton, List.getElem?_eq_getElem bound,
      Option.map_some, Option.getD_some]
    congr 1
    by_cases h : route[i] = direction
    · simp [h]
    · simp [h]
  · have le : route.length ≤ i := by omega
    simp [List.take_of_length_le le, List.take_of_length_le (by omega : route.length ≤ i+1),
      List.getElem?_eq_none (by omega : route.length ≤ i)]

def vertexSuccessorCountColumn (direction : AxisDirection) :
    Compiler (fun s => vertexRows (rows s) (directions s))
      (fun s row => ((directions s row.1).take (row.2 + 1)).count direction) := by
  let physical := UnaryColumn.add (vertexCountColumn rows directions routesCompiler direction)
    (vertexDirectionValueCompiler rows directions routesCompiler
      (fun next => (next.map (fun d => if d = direction then 1 else 0)).getD 0))
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  apply List.map_congr_left
  intro row _
  exact (count_take_next direction (directions s row.1) row.2).symm

end LeanTrominoes.DelimitedDirectionDisplacement
end
