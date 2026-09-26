/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.DelimitedDirectionVertexCompiler
import LeanTrominoes.FiniteBlockIndexShapeSemantics

/-! # Route and within-route indices for the native segment table -/
noncomputable section
namespace LeanTrominoes.DelimitedDirectionDisplacement
open Computability Turing UnaryColumn

private theorem sum_counts (route : List AxisDirection) :
    route.count .east + route.count .north + route.count .west + route.count .south +
      route.count .invalid = route.length := by
  induction route with
  | nil => rfl
  | cons direction route ih =>
      cases direction <;> simp at * <;> omega

variable {Symbol Index : Type} [Fintype Symbol] [Inhabited Symbol]
    (rows : List Symbol → List Index) (directions : List Symbol → Index → List AxisDirection)
    (routesCompiler : TM2ComputableInPolyTime id id (fun s => words ((rows s).map (directions s))))

def vertexLocalIndexCompiler : Compiler (fun s => vertexRows (rows s) (directions s)) (fun _ row => row.2) := by
  let physical := UnaryColumn.add (UnaryColumn.add (UnaryColumn.add (UnaryColumn.add
    (vertexCountColumn rows directions routesCompiler .east)
    (vertexCountColumn rows directions routesCompiler .north))
    (vertexCountColumn rows directions routesCompiler .west))
    (vertexCountColumn rows directions routesCompiler .south))
    (vertexCountColumn rows directions routesCompiler .invalid)
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  apply List.map_congr_left
  intro row member
  dsimp only
  rw [sum_counts, List.length_take]
  have bound : row.2 ≤ (directions s row.1).length := by
    simp only [vertexRows, List.mem_flatMap, List.mem_map] at member
    obtain ⟨parent, _, i, hi, equal⟩ := member
    cases equal
    have := List.mem_range.mp hi
    dsimp only
    omega
  exact Nat.min_eq_left bound

def vertexParentIndexCompiler :
    Compiler (fun s => vertexRows (rows s).zipIdx (fun row => directions s row.1))
      (fun _ row => row.1.2) := by
  apply TM2ComputableInPolyTime.of_eq
    (vertexParentsCompiler (fun s => (rows s).map (directions s)) routesCompiler)
  intro s
  rw [vertexParents, FiniteBlockIndices.indices_eq_expected, FiniteBlockIndices.expected,
    FiniteBlockIndices.expectedAux_eq_zipIdx_replicate _ _ _ (by simp)]
  simp only [List.zipIdx_map, List.flatMap_map, vertexRows, List.map_flatMap,
    List.map_map, Function.comp_def, Prod.map, id_eq]
  simp only [List.map_const', List.length_range]

end LeanTrominoes.DelimitedDirectionDisplacement
end
