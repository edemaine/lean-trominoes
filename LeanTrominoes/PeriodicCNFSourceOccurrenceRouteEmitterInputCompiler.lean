/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterInput
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteTokenCompiler
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteTokenCounts
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteTokenSourceSemantics
import LeanTrominoes.PeriodicCNFSourceOccurrenceTargetVertexIndexCompiler
import LeanTrominoes.PeriodicCNFSourceOccurrenceTargetVertexIndexSemantics
import LeanTrominoes.TM2ForkMachineTime
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Polynomial-time source-occurrence route-emitter inputs -/

noncomputable section

namespace LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitter

open Computability Turing

local instance : Inhabited
    SourceSplitRouteDescriptorTokens.finEncoding.Γ :=
  ⟨PartrecToTM2.Γ'.bit0⟩

/-- Exact route-emitter input prepared from a promised flat source. -/
def sourceInput
    (source : SourceSplitRouteDescriptorTokens.Source) : Input where
  occurrences := SourceOccurrenceRouteTokens.sourceTokens source
  targets := SourceOccurrenceTargetVertexIndices.indices source
  valid := by
    rw [SourceOccurrenceTargetVertexIndices.indices_length,
      SourceOccurrenceRouteTokens.sourceTokens_eq_formulaTokens,
      SourceOccurrenceRouteTokens.selectedCount_isLiteral_formulaTokens]
    simp [SourceOccurrenceAtomRanks.occurrenceAtoms]

@[simp] theorem sourceInput_occurrences
    (source : SourceSplitRouteDescriptorTokens.Source) :
    (sourceInput source).occurrences =
      SourceOccurrenceRouteTokens.sourceTokens source := rfl

@[simp] theorem sourceInput_targets
    (source : SourceSplitRouteDescriptorTokens.Source) :
    (sourceInput source).targets =
      SourceOccurrenceTargetVertexIndices.indices source := rfl

/-- The normalized finite occurrence stream and its aligned target indices
can be produced together in polynomial time. -/
noncomputable def sourceInputComputableInPolyTime :
    TM2ComputableInPolyTime
      SourceSplitRouteDescriptorTokens.finEncoding.encode encode sourceInput := by
  let paired := TM2ForkMachine.computableInPolyTime
    SourceOccurrenceRouteTokens.sourceTokensComputableInPolyTime
    SourceOccurrenceTargetVertexIndices.unaryFieldsComputableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq paired
    (fun _ => by rfl)

end LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitter

end
