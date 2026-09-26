/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.DelimitedDirectionVertexCompiler
import LeanTrominoes.UnaryFieldFirstBlockFilter

/-! # First-vertex flags and route-length headers -/
noncomputable section
namespace LeanTrominoes.DelimitedDirectionDisplacement
open Computability Turing FiniteStateTransducer UnaryColumn

private def firstTransition (first : Bool) : Token → Bool × List Bool
  | .direction _ => (false, [first])
  | .routeEnd => (true, [first])

private theorem scan_first_word (first : Bool) (route : List AxisDirection) :
    scan firstTransition first (word route) = (true, first :: List.replicate route.length false) := by
  induction route generalizing first with
  | nil => simp [word, scan, firstTransition]
  | cons direction route ih =>
      simpa [word, scan, firstTransition, List.replicate_succ] using
        congrArg (fun result : Bool × List Bool => (result.1, first :: result.2)) (ih false)

private theorem scan_first_words (routes : List (List AxisDirection)) :
    scan firstTransition true (words routes) =
      (true, routes.flatMap (fun route => UnaryFieldBooleanFilter.firstBlockControls (route.length + 1))) := by
  induction routes with
  | nil => rfl
  | cons route routes ih =>
      simp only [words, List.flatMap_cons] at ih ⊢
      simp only [scan_append, scan_first_word]
      rw [ih]
      simp [UnaryFieldBooleanFilter.firstBlockControls_succ]

def firstVerticesCompiler {Symbol : Type} [Fintype Symbol]
    (routes : List Symbol → List (List AxisDirection))
    (compiler : TM2ComputableInPolyTime id id (fun input => words (routes input))) :
    TM2ComputableInPolyTime id id (fun input => (routes input).flatMap
      (fun route => UnaryFieldBooleanFilter.firstBlockControls (route.length + 1))) := by
  let physical := TM2CompositionMachine.computableInPolyTime compiler
    (FiniteStateTransducer.computableInPolyTime true firstTransition (fun _ => []))
  apply TM2ComputableInPolyTime.of_eq physical
  intro input
  simp only [output, scan_first_words, List.append_nil]

variable {Symbol Index : Type} [Fintype Symbol] [Inhabited Symbol]
    (rows : List Symbol → List Index) (directions : List Symbol → Index → List AxisDirection)
    (routesCompiler : TM2ComputableInPolyTime id id (fun s => words ((rows s).map (directions s))))

def vertexFirstColumn : TM2ComputableInPolyTime id id (fun s =>
    (vertexRows (rows s) (directions s)).map (fun row => decide (row.2 = 0))) := by
  apply TM2ComputableInPolyTime.of_eq
    (firstVerticesCompiler (fun s => (rows s).map (directions s)) routesCompiler)
  intro s
  simp only [vertexRows, UnaryFieldBooleanFilter.firstBlockControls,
    List.flatMap_map, List.map_flatMap, List.map_map, Function.comp_def]

def vertexLengthColumn : Compiler (fun s => vertexRows (rows s) (directions s))
    (fun s row => (directions s row.1).length + 1) := by
  apply vertexBroadcastColumn rows directions routesCompiler
    (value := fun s row => (directions s row).length + 1)
  apply TM2ComputableInPolyTime.of_eq
    (vertexLengthsCompiler (fun s => (rows s).map (directions s)) routesCompiler)
  intro s
  simp only [List.map_map, Function.comp_def]

theorem vertexFrame (count : Nat) (fields : Nat → List Nat) :
    (List.range (count + 1)).flatMap (fun index =>
      (if index = 0 then [count + 1] else []) ++ fields index) =
      (count + 1) :: (List.range (count + 1)).flatMap fields := by
  simp [List.range_succ_eq_map, List.flatMap_map]

end LeanTrominoes.DelimitedDirectionDisplacement
end
