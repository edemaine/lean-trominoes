/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.DelimitedDirectionSegmentCoordinates
import LeanTrominoes.DelimitedDirectionSegmentGeometry
import LeanTrominoes.DelimitedDirectionVertexIndices
import LeanTrominoes.UnaryOptionalBlocksCompiler

/-! # Polynomial-time serialization of the indexed segment table -/
noncomputable section
namespace LeanTrominoes.DelimitedDirectionDisplacement
open Computability Turing UnaryColumn
open UnaryFieldEncoderMachine (unaryField unaryFields)

def segmentTableFields (routes : List (List Cell)) : List Nat :=
  routes.zipIdx.flatMap (fun route => (gridPolylineSegments route.1).zipIdx.flatMap
    (fun segment => PeriodicGridDrawing.Arithmetic.segmentFields ⟨route.2, segment.2, segment.1⟩))

theorem segmentTableFields_drawing (drawing : PeriodicGridDrawing) :
    segmentTableFields drawing.edgeRoutes =
      drawing.indexedSegments.flatMap PeriodicGridDrawing.Arithmetic.segmentFields := by
  simp only [segmentTableFields, PeriodicGridDrawing.indexedSegments, List.flatMap_assoc, List.flatMap_map]

variable {Symbol Index : Type} [Fintype Symbol] [Inhabited Symbol]
    (rows : List Symbol → List Index) (directions : List Symbol → Index → List AxisDirection)
    (start : List Symbol → Index → Cell)
    (routesCompiler : TM2ComputableInPolyTime id id (fun s => words ((rows s).map (directions s))))
    (xp : Compiler rows (fun s row => (start s row).1.toNat))
    (xn : Compiler rows (fun s row => (-(start s row).1).toNat))
    (yp : Compiler rows (fun s row => (start s row).2.toNat))
    (yn : Compiler rows (fun s row => (-(start s row).2).toNat))

def segmentVertexBlocks : BlocksCompiler
    (fun s => vertexRows (rows s).zipIdx (fun row => directions s row.1))
    (fun s row => unaryFields (PeriodicGridDrawing.Arithmetic.segmentFields
      ⟨row.1.2, row.2, vertexSegment (start s row.1.1) (directions s row.1.1) row.2⟩)) := by
  let tagged := tagRouteWordsCompiler rows directions routesCompiler
  let xs := vertexCoordinateCodeCompiler (fun s => (rows s).zipIdx)
    (fun s row => directions s row.1) (fun s row => start s row.1) tagged true
    (tagRouteColumn rows xp) (tagRouteColumn rows xn)
  let ys := vertexCoordinateCodeCompiler (fun s => (rows s).zipIdx)
    (fun s row => directions s row.1) (fun s row => start s row.1) tagged false
    (tagRouteColumn rows yp) (tagRouteColumn rows yn)
  let xf := vertexSuccessorCoordinateCodeCompiler (fun s => (rows s).zipIdx)
    (fun s row => directions s row.1) (fun s row => start s row.1) tagged true
    (tagRouteColumn rows xp) (tagRouteColumn rows xn)
  let yf := vertexSuccessorCoordinateCodeCompiler (fun s => (rows s).zipIdx)
    (fun s row => directions s row.1) (fun s row => start s row.1) tagged false
    (tagRouteColumn rows yp) (tagRouteColumn rows yn)
  let indices := vertexLocalIndexCompiler (fun s => (rows s).zipIdx) (fun s row => directions s row.1) tagged
  let physical := appendBlocks (blocks (vertexParentIndexCompiler rows directions routesCompiler))
    (appendBlocks (blocks indices) (appendBlocks (blocks xs) (appendBlocks (blocks ys)
      (appendBlocks (blocks xf) (blocks yf)))))
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  simp only [PeriodicGridDrawing.Arithmetic.segmentFields, vertexSegment, component,
    Bool.false_eq_true, ↓reduceIte, UnaryFieldEncoderMachine.unaryFields_cons,
    UnaryFieldEncoderMachine.unaryFields_nil, List.append_nil]

private theorem optional_encoded (keep : Prop) [Decidable keep] (fields : List Nat) :
    (if keep then unaryFields fields else []) = unaryFields (if keep then fields else []) := by
  by_cases h : keep <;> simp [h]

def segmentFieldsCompiler : TM2ComputableInPolyTime id unaryFields (fun s =>
    segmentTableFields ((rows s).map (fun row => Gadget.rebuildRoute (start s row) (directions s row)))) := by
  let control := vertexHasSuccessorCompiler (fun s => (rows s).zipIdx) (fun s row => directions s row.1)
    (tagRouteWordsCompiler rows directions routesCompiler)
  let physical := finishBlocks (UnaryOptionalBlocks.compiler control
    (segmentVertexBlocks rows directions start routesCompiler xp xn yp yn))
  apply TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq physical
  intro s
  simp only [id_eq, optional_encoded, decide_eq_true_eq]
  have flattenFields {A : Type} (items : List A) (f : A → List Nat) :
      items.flatMap (fun item => unaryFields (f item)) = unaryFields (items.flatMap f) := by
    simp only [unaryFields, List.flatMap_assoc]
  rw [flattenFields]
  congr 1
  simp only [vertexRows, List.flatMap_assoc, List.flatMap_map, segmentFrame,
    segmentTableFields, List.zipIdx_map, Prod.map, id_eq]
  apply List.flatMap_congr
  intro row _
  have segments := congrArg (List.flatMap PeriodicGridDrawing.Arithmetic.segmentFields)
    (rebuildRoute_indexedSegments (start s row.1) (directions s row.1) row.2)
  simpa only [List.flatMap_map] using segments.symm

end LeanTrominoes.DelimitedDirectionDisplacement
end
