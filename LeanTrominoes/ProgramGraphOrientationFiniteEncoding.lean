/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.ProgramGraphOrientationEndpointFields
import LeanTrominoes.TrichromaticGraphOrientationFieldsCompiler
import LeanTrominoes.TrichromaticGraphOrientationFinite
import LeanTrominoes.UnaryColumnFiveCompiler
import LeanTrominoes.FiniteProgramSparseTrominoRegion

/-! # Native finite graph records from a zero-offset program source -/
noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Turing Gadget PeriodicThreeDM UnaryColumn
variable {Source : Type} {encoding : _root_.LeanTrominoes.FiniteEncoding Source} {language : Source → Prop}
variable (source : PeriodicCNF.ProgramSource encoding language)
variable (zero : ∀ symbols, FiniteCNF.ZeroOffsets (source.formulaOfSymbols symbols))
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 2048

def programOrientationGraph (symbols : List encoding.Γ) : TrichromaticGraphOrientation.Input :=
  GraphOrientationEncoding.input (programThreeDMProblem source symbols)

include zero in
theorem programThreeDM_zeroOffsets (symbols : List encoding.Γ) :
    (programThreeDMProblem source symbols).ZeroOffsets := by
  rw [programThreeDMProblem,horizontalThreeDMProblemComputed_eq_problem]
  exact FiniteProgramSparseTrominoRegion.problemZero source zero symbols

include zero in
theorem programOrientationGraph_zeroOffsets (symbols : List encoding.Γ) :
    TrichromaticGraphOrientation.ZeroOffsets (programOrientationGraph source symbols) :=
  GraphOrientationEncoding.input_zeroOffsets (programThreeDM_zeroOffsets source zero symbols)

include zero in
theorem programOrientationGraph_finite_correct (symbols : List encoding.Γ) :
    TrichromaticGraphOrientation.FiniteProblem (programOrientationGraph source symbols) ↔
      PeriodicCNF.LocalPeriodicCNF1DSAT (source.formulaOfSymbols symbols) := by
  rw [TrichromaticGraphOrientation.finiteProblem_iff (programOrientationGraph_zeroOffsets source zero symbols)]
  change TrichromaticGraphOrientation.Problem (GraphOrientationEncoding.input (programThreeDMProblem source symbols)) ↔ _
  rw [GraphOrientationEncoding.problem_iff _ (programThreeDMWellFormed source symbols) (programThreeDMDegree source symbols),
    programThreeDMProblem,horizontalThreeDMProblemComputed_eq_problem]
  exact (problem_correct _).symm

variable [Inhabited encoding.Γ]

def programOrientationFiniteBodyCompiler : TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
    (fun s => (programOrientationGraph source s).2.flatMap TrichromaticGraphOrientation.FlatEncoding.edgeFields) := by
  let physical := five (programSourceFieldCompiler source) (programTargetFieldCompiler source)
    (constant (programContractedColorCompiler source) 0) (constant (programContractedColorCompiler source) 0)
    (programContractedColorCompiler source)
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  simp only [programOrientationGraph,GraphOrientationEncoding.input,List.flatMap_map]
  apply List.flatMap_congr
  intro edge member
  have offset := contractedEdge_offset_eq_zero (programThreeDM_zeroOffsets source zero s) member
  simp only [GraphOrientationEncoding.edgeRecord,TrichromaticGraphOrientation.FlatEncoding.edgeFields,offset]
  rfl

def programOrientationFiniteFieldsCompiler : TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
    (fun s => TrichromaticGraphOrientation.FlatEncoding.fields (programOrientationGraph source s)) := by
  let vertices : ScalarCompiler (fun s => (programOrientationGraph source s).1.length) := by
    apply TM2ComputableInPolyTime.of_eq (programVertexCountCompiler source)
    intro s
    simp only [programOrientationGraph,GraphOrientationEncoding.input,List.length_map]
  let edges : ScalarCompiler (fun s => (programOrientationGraph source s).2.length) := by
    apply TM2ComputableInPolyTime.of_eq (countRows (programContractedColorCompiler source))
    intro s
    simp only [programOrientationGraph,GraphOrientationEncoding.input,List.length_map]
  let kinds : TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (fun s => (programOrientationGraph source s).1.map Bool.toNat) := by
    apply TM2ComputableInPolyTime.of_eq (programVertexKindCompiler source)
    intro s
    simp only [programOrientationGraph,GraphOrientationEncoding.input,List.map_map,Function.comp_def]
  exact TrichromaticGraphOrientation.FlatEncoding.fieldsCompiler (graph := programOrientationGraph source)
    vertices edges kinds (programOrientationFiniteBodyCompiler source zero)

def programOrientationFiniteEncodingCompiler : TM2ComputableInPolyTime id
    TrichromaticGraphOrientation.FlatEncoding.finEncoding.encode (programOrientationGraph source) :=
  TrichromaticGraphOrientation.FlatEncoding.encodingCompiler (graph := programOrientationGraph source)
    (programOrientationFiniteFieldsCompiler source zero)

end LeanTrominoes.PeriodicCNFStripReduction
end
