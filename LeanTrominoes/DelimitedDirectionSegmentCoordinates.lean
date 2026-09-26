/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.DelimitedDirectionVertexSuccessor

/-! # Native coordinate codes for each segment's successor endpoint -/
noncomputable section
namespace LeanTrominoes.DelimitedDirectionDisplacement
open Computability Turing UnaryColumn
variable {Symbol Index : Type} [Fintype Symbol] [Inhabited Symbol]
    (rows : List Symbol → List Index) (directions : List Symbol → Index → List AxisDirection)
    (start : List Symbol → Index → Cell)
    (routesCompiler : TM2ComputableInPolyTime id id (fun s => words ((rows s).map (directions s))))

def vertexSuccessorCoordinateCodeCompiler (horizontal : Bool)
    (positive : Compiler rows (fun s row => (component horizontal (start s row)).toNat))
    (negative : Compiler rows (fun s row => (-component horizontal (start s row)).toNat)) :
    Compiler (fun s => vertexRows (rows s) (directions s))
      (fun s row => Encodable.encode (component horizontal
        (vertexPoint (start s row.1) (directions s row.1) (row.2 + 1)))) := by
  let cp := UnaryColumn.add (vertexBroadcastColumn rows directions routesCompiler positive)
    (vertexSuccessorCountColumn rows directions routesCompiler (axisDirection horizontal true))
  let cn := UnaryColumn.add (vertexBroadcastColumn rows directions routesCompiler negative)
    (vertexSuccessorCountColumn rows directions routesCompiler (axisDirection horizontal false))
  let physical := signedDifference cp cn
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  apply List.map_congr_left
  intro row _
  dsimp only
  rw [vertexPoint_component, displacement_eq_counts]
  congr 1
  push_cast
  omega

/-- True precisely at vertices with a successor, so no segment crosses a route boundary. -/
def vertexHasSuccessorCompiler : TM2ComputableInPolyTime id id (fun s =>
    (vertexRows (rows s) (directions s)).map (fun row => decide (row.2 < (directions s row.1).length))) := by
  let physical := bits (vertexDirectionValueCompiler rows directions routesCompiler (fun next => next.isSome.toNat))
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  apply List.map_congr_left
  intro row _
  simp

/-- Tagging routes with their ordinal leaves their compiled coordinate column unchanged. -/
def tagRouteColumn {value : List Symbol → Index → Nat} (compiler : Compiler rows value) :
    Compiler (fun s => (rows s).zipIdx) (fun s row => value s row.1) := by
  apply TM2ComputableInPolyTime.of_eq compiler
  intro s
  simpa only [List.map_map, Function.comp_def] using
    (congrArg (List.map (value s)) (List.zipIdx_map_fst 0 (rows s))).symm

def tagRouteWordsCompiler : TM2ComputableInPolyTime id id (fun s =>
    words ((rows s).zipIdx.map (fun row => directions s row.1))) := by
  apply TM2ComputableInPolyTime.of_eq routesCompiler
  intro s
  congr 1
  simpa only [List.map_map, Function.comp_def] using
    (congrArg (List.map (directions s)) (List.zipIdx_map_fst 0 (rows s))).symm

end LeanTrominoes.DelimitedDirectionDisplacement
end
