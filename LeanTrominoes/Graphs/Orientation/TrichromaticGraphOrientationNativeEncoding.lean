/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Orientation.TrichromaticGraphOrientationNativeOffsetFields
import LeanTrominoes.Graphs.Orientation.TrichromaticGraphOrientationLineReduction
import LeanTrominoes.Computation.Encoding.Unary.UnaryColumnFiveCompiler
import LeanTrominoes.Graphs.Orientation.TrichromaticGraphOrientationFieldsCompiler

/-! # The native binary graph compiler for the PSPACE reduction -/
noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Turing Gadget PeriodicThreeDM UnaryColumn
variable {Input : Type} {encoding : _root_.LeanTrominoes.FiniteEncoding Input} {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language) [Inhabited encoding.Γ]
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 2048

def nativeOrientationBodyCompiler : TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
    (fun s => (nativeOrientationGraph decider s).2.flatMap TrichromaticGraphOrientation.FlatEncoding.edgeFields) := by
  let physical := five (nativeSourceFieldCompiler decider) (nativeTargetFieldCompiler decider)
    (nativeEdgeOffsetCompiler decider true) (nativeEdgeOffsetCompiler decider false)
    (nativeContractedColorCompiler decider)
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  simp [nativeOrientationGraph,GraphOrientationEncoding.input,GraphOrientationEncoding.edgeRecord,
    TrichromaticGraphOrientation.FlatEncoding.edgeFields,List.flatMap_map,DelimitedDirectionDisplacement.component]

def nativeOrientationFieldsCompiler : TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
    (fun s => TrichromaticGraphOrientation.FlatEncoding.fields (nativeOrientationGraph decider s)) := by
  let vertices : ScalarCompiler (fun s => (nativeOrientationGraph decider s).1.length) := by
    apply TM2ComputableInPolyTime.of_eq (nativeVertexCountCompiler decider)
    intro s
    simp only [nativeOrientationGraph,GraphOrientationEncoding.input,List.length_map]
  let edges : ScalarCompiler (fun s => (nativeOrientationGraph decider s).2.length) := by
    apply TM2ComputableInPolyTime.of_eq (countRows (nativeContractedColorCompiler decider))
    intro s
    simp only [nativeOrientationGraph,GraphOrientationEncoding.input,List.length_map]
  let kinds : TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (fun s => (nativeOrientationGraph decider s).1.map Bool.toNat) := by
    apply TM2ComputableInPolyTime.of_eq (nativeVertexKindCompiler decider)
    intro s
    simp only [nativeOrientationGraph,GraphOrientationEncoding.input,List.map_map,Function.comp_def]
  exact TrichromaticGraphOrientation.FlatEncoding.fieldsCompiler (graph := nativeOrientationGraph decider)
    vertices edges kinds (nativeOrientationBodyCompiler decider)

def nativeOrientationEncodingCompiler : TM2ComputableInPolyTime id
    TrichromaticGraphOrientation.FlatEncoding.finEncoding.encode (nativeOrientationGraph decider) :=
  TrichromaticGraphOrientation.FlatEncoding.encodingCompiler (graph := nativeOrientationGraph decider)
    (nativeOrientationFieldsCompiler decider)

end LeanTrominoes.PeriodicCNFStripReduction
end
