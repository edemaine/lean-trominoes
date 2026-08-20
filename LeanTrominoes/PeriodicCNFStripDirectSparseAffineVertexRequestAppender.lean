/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseAffineVertexWorkspaceCompiler
import LeanTrominoes.PeriodicCNFStripDirectSparseAffineVertexRequestData
import LeanTrominoes.PeriodicCNFStripDirectSparseRecordAppenderData

/-! # Compact affine request interface for the direct vertex appender -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSparseAffineRequestAppenderStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The remaining direct vertex machine may emit compact affine requests
while retaining the original source word. -/
abbrev DirectSparseAffineVertexRequestAppender :=
  TM2ComputableInPolyTime id id
    (RetainedInputAppendPipeline.appended
      (directSparseComputedAffineVertexRequestsOfSymbols decider))

/-- A compact request appender followed by fixed retained-source affine
expansion satisfies the existing canonical vertex-record appender contract. -/
noncomputable def directSparseVertexRecordAppenderOfAffineRequests
    (requests : DirectSparseAffineVertexRequestAppender decider) :
    DirectSparseVertexRecordAppender decider := by
  let expanded := TM2CompositionMachine.computableInPolyTime requests
    (GadgetSparseAffineVertexWorkspace.computableInPolyTime
      (Source := encoding.Γ))
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq expanded
    (fun symbols => by
      rw [GadgetSparseAffineVertexWorkspace.expand_appended]
      simp only [id_eq]
      unfold RetainedInputAppendPipeline.appended
      change RetainedInputAppendPipeline.embed symbols ++
          (GadgetSparseAffineVertexTokens.expand
            (directSparseComputedAffineVertexRequestsOfSymbols
              decider symbols)).map Sum.inr =
        RetainedInputAppendPipeline.embed symbols ++
          (directSparseComputedVertexRecordsOfSymbols
            decider symbols).map Sum.inr
      rw [expand_directSparseComputedAffineVertexRequestsOfSymbols])

end PeriodicCNFStripReduction
end LeanTrominoes
