/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.DelimitedDirectionVertexHeaders
import LeanTrominoes.UnaryOptionalBlocksCompiler

/-! # Complete native route fields, with point-count headers -/
noncomputable section
namespace LeanTrominoes.DelimitedDirectionDisplacement
open Computability Turing UnaryColumn
open UnaryFieldEncoderMachine (unaryFields unaryField)
variable {Symbol Index : Type} [Fintype Symbol] [Inhabited Symbol]
    (rows : List Symbol → List Index) (directions : List Symbol → Index → List AxisDirection)
    (start : List Symbol → Index → Cell)
    (routesCompiler : TM2ComputableInPolyTime id id (fun s => words ((rows s).map (directions s))))
    (xp : Compiler rows (fun s row => (start s row).1.toNat))
    (xn : Compiler rows (fun s row => (-(start s row).1).toNat))
    (yp : Compiler rows (fun s row => (start s row).2.toNat))
    (yn : Compiler rows (fun s row => (-(start s row).2).toNat))

private theorem encoded_vertex_frame (length index : Nat) (point : Cell) :
    (if decide (index = 0) then unaryField length else []) ++
      (unaryField (Encodable.encode point.1) ++ unaryField (Encodable.encode point.2)) =
    unaryFields ((if index = 0 then [length] else []) ++ PeriodicGridDrawing.Arithmetic.pointFields point) := by
  by_cases h : index = 0 <;> simp [h, unaryFields, PeriodicGridDrawing.Arithmetic.pointFields]

def routeFieldsCompiler : TM2ComputableInPolyTime id unaryFields (fun s =>
    (rows s).flatMap (fun row => PeriodicGridDrawing.Arithmetic.routeFields
      (Gadget.rebuildRoute (start s row) (directions s row)))) := by
  let headers := UnaryOptionalBlocks.compiler (vertexFirstColumn rows directions routesCompiler)
    (blocks (vertexLengthColumn rows directions routesCompiler))
  let coordinates := appendBlocks
    (blocks (vertexCoordinateCodeCompiler rows directions start routesCompiler true xp xn))
    (blocks (vertexCoordinateCodeCompiler rows directions start routesCompiler false yp yn))
  let physical := finishBlocks (appendBlocks headers coordinates)
  apply TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq physical
  intro s
  simp only [id_eq, component, Bool.false_eq_true, ↓reduceIte, encoded_vertex_frame]
  have flattenFields {A : Type} (items : List A) (f : A → List Nat) :
      items.flatMap (fun item => unaryFields (f item)) = unaryFields (items.flatMap f) := by
    simp only [unaryFields, List.flatMap_assoc]
  rw [flattenFields]
  congr 1
  simp only [vertexRows, List.flatMap_assoc, List.flatMap_map]
  apply List.flatMap_congr
  intro row _
  rw [vertexFrame]
  simp only [PeriodicGridDrawing.Arithmetic.routeFields, rebuildRoute_eq_vertices,
    List.flatMap_map, List.length_map, List.length_range]

end LeanTrominoes.DelimitedDirectionDisplacement
end
