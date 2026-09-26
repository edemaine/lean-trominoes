/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.DelimitedDirectionVertexGeometry
import LeanTrominoes.DelimitedDirectionVertexBroadcast
import LeanTrominoes.UnaryPointFieldsCompiler

/-! # Polynomial-time coordinate fields for every reconstructed route vertex -/
noncomputable section
namespace LeanTrominoes.DelimitedDirectionDisplacement
open Computability Turing UnaryColumn
open UnaryFieldEncoderMachine (unaryFields)
variable {Symbol Index : Type} [Fintype Symbol] [Inhabited Symbol]
    (rows : List Symbol → List Index)
    (directions : List Symbol → Index → List AxisDirection)
    (start : List Symbol → Index → Cell)
    (routesCompiler : TM2ComputableInPolyTime id id
      (fun s => words ((rows s).map (directions s))))

/-- Cumulative counts aligned to the common indexed vertex rows. -/
def vertexCountColumn (direction : AxisDirection) :
    Compiler (fun s => vertexRows (rows s) (directions s))
      (fun s row => ((directions s row.1).take row.2).count direction) := by
  let physical := vertexCountsCompiler (fun s => (rows s).map (directions s)) direction routesCompiler
  exact TM2ComputableInPolyTime.of_eq physical (fun s => vertexRows_counts _ _ direction)

/-- An independently compiled per-route value can be reused at every vertex. -/
def vertexBroadcastColumn {value : List Symbol → Index → Nat}
    (compiler : Compiler rows value) :
    Compiler (fun s => vertexRows (rows s) (directions s)) (fun s row => value s row.1) := by
  let physical := broadcastVerticesCompiler (fun s => (rows s).map (directions s))
    (fun s => (rows s).map (value s)) (fun s => by simp) routesCompiler compiler
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  rw [broadcastVertices_map, vertexRows_constant]

/-- Both positive and negative path contributions are retained until signed encoding. -/
def vertexCoordinateCodeCompiler (horizontal : Bool)
    (positive : Compiler rows (fun s row => (component horizontal (start s row)).toNat))
    (negative : Compiler rows (fun s row => (-component horizontal (start s row)).toNat)) :
    Compiler (fun s => vertexRows (rows s) (directions s))
      (fun s row => Encodable.encode (component horizontal
        (vertexPoint (start s row.1) (directions s row.1) row.2))) := by
  let cp := UnaryColumn.add (vertexBroadcastColumn rows directions routesCompiler positive)
    (vertexCountColumn rows directions routesCompiler (axisDirection horizontal true))
  let cn := UnaryColumn.add (vertexBroadcastColumn rows directions routesCompiler negative)
    (vertexCountColumn rows directions routesCompiler (axisDirection horizontal false))
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

/-- Complete point fields in route-major, vertex-minor order. -/
def vertexPointFieldsCompiler
    (xp : Compiler rows (fun s row => (start s row).1.toNat))
    (xn : Compiler rows (fun s row => (-(start s row).1).toNat))
    (yp : Compiler rows (fun s row => (start s row).2.toNat))
    (yn : Compiler rows (fun s row => (-(start s row).2).toNat)) :
    TM2ComputableInPolyTime id unaryFields (fun s =>
      (rows s).flatMap (fun row => (Gadget.rebuildRoute (start s row) (directions s row)).flatMap
        PeriodicGridDrawing.Arithmetic.pointFields)) := by
  let physical := pairFields
    (vertexCoordinateCodeCompiler rows directions start routesCompiler true xp xn)
    (vertexCoordinateCodeCompiler rows directions start routesCompiler false yp yn)
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  simp only [vertexRows, List.flatMap_assoc, List.flatMap_map, rebuildRoute_eq_vertices,
    PeriodicGridDrawing.Arithmetic.pointFields, component, Bool.false_eq_true, ↓reduceIte]

end LeanTrominoes.DelimitedDirectionDisplacement
end
