/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseAffineIndexedEmitterCompiler
import LeanTrominoes.GadgetSparseAffineIndexedEmitterPipelineData
import LeanTrominoes.PeriodicCNFAffineEmitterPipeline

/-! # Polynomial-time pipelines of indexed affine-record phases -/

noncomputable section

namespace LeanTrominoes
namespace GadgetSparseAffineIndexedEmitter

open Computability Turing

/-- Flattening one nested affine-record workspace is a fixed finite block
transduction. -/
noncomputable def flattenComputableInPolyTime
    {Data : Type} [Fintype Data] [Inhabited Data] :
    @TM2ComputableInPolyTime
      (List (PhaseWorkspace Data ⊕
        GadgetSparseAffineVertexTokens.Token))
      (List (PhaseWorkspace Data))
      (PhaseWorkspace Data ⊕ GadgetSparseAffineVertexTokens.Token)
      (PhaseWorkspace Data) id id
      (flattenWorkspace (Data := Data)) :=
  FiniteBlockTransducer.computableInPolyTime flattenItem

/-- One indexed family is a polynomial-time append-only phase on the shared
retained workspace. -/
noncomputable def phaseComputableInPolyTime
    {Data : Type} [Fintype Data] [Inhabited Data]
    (family : RecordFamily Data) :
    @TM2ComputableInPolyTime
      (List (PhaseWorkspace Data)) (List (PhaseWorkspace Data))
      (PhaseWorkspace Data) (PhaseWorkspace Data) id id
      (phaseRun family) := by
  let emitted := recordsComputableInPolyTime (workspaceFamily family)
  let flattened := TM2CompositionMachine.computableInPolyTime emitted
    (flattenComputableInPolyTime (Data := Data))
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq flattened
    (fun workspace => by
      exact flattenWorkspace_recordsAppended family workspace)

/-- Any fixed finite sequence of indexed affine-record phases is polynomial
time on the shared retained workspace. -/
noncomputable def runPhasesComputableInPolyTime
    {Data : Type} [Fintype Data] [Inhabited Data]
    (families : List (RecordFamily Data)) :
    @TM2ComputableInPolyTime
      (List (PhaseWorkspace Data)) (List (PhaseWorkspace Data))
      (PhaseWorkspace Data) (PhaseWorkspace Data) id id
      (runPhases families) := by
  induction families with
  | nil =>
      exact PeriodicCNF.AffineEmitterPipeline.identityComputableInPolyTime
  | cons family families induction =>
      let composed := TM2CompositionMachine.computableInPolyTime
        (phaseComputableInPolyTime family) induction
      simpa only [runPhases] using composed

/-- Embed the finite scan stream once, execute all indexed phases in order,
and retain only their concatenated compact-record output. -/
noncomputable def emittedPhasesComputableInPolyTime
    {Data : Type} [Fintype Data] [Inhabited Data]
    (families : List (RecordFamily Data)) :
    @TM2ComputableInPolyTime
      (List Data) (List GadgetSparseAffineVertexTokens.Token)
      Data GadgetSparseAffineVertexTokens.Token id id
      (emittedPhases families) := by
  let embedded := RetainedInputAppendPipeline.embedComputableInPolyTime
    (Source := Data) (Target := GadgetSparseAffineVertexTokens.Token)
  let throughPhases := TM2CompositionMachine.computableInPolyTime embedded
    (runPhasesComputableInPolyTime families)
  let complete := TM2CompositionMachine.computableInPolyTime throughPhases
    (RetainedInputAppendPipeline.extractComputableInPolyTime
      (Source := Data) (Target := GadgetSparseAffineVertexTokens.Token))
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq complete
    (fun data => by rfl)

end GadgetSparseAffineIndexedEmitter
end LeanTrominoes
