/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceClauseCountFieldCompiler
import LeanTrominoes.PeriodicCNFSourceCycleLinkPositionTagSourceCompiler
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterInput
import LeanTrominoes.PeriodicCNFSourceCycleLinkTargetIndexCompiler
import LeanTrominoes.TM2ForkMachineTime
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Polynomial-time tagged source cycle-link emitter inputs -/

noncomputable section

namespace LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitter

open Turing

local instance : Inhabited
    SourceSplitRouteDescriptorTokens.finEncoding.Γ :=
  ⟨PartrecToTM2.Γ'.bit0⟩

local instance : Inhabited HeaderSymbol := ⟨.separator⟩

def sourceInput (source : SourceSplitRouteDescriptorTokens.Source) : Input where
  clauseCount := source.formula.clauses.length
  tags := SourceCycleLinkPositionTags.tags
    (SourceOccurrenceAtomGroupSizes.sizes source)
  targets := SourceCycleLinkTargetIndices.targetIndices
    (SourceOccurrenceAtomGroupSizes.sizes source)
  valid := by simp

@[simp] theorem sourceInput_clauseCount
    (source : SourceSplitRouteDescriptorTokens.Source) :
    (sourceInput source).clauseCount = source.formula.clauses.length := rfl

@[simp] theorem sourceInput_tags
    (source : SourceSplitRouteDescriptorTokens.Source) :
    (sourceInput source).tags = SourceCycleLinkPositionTags.tags
      (SourceOccurrenceAtomGroupSizes.sizes source) := rfl

@[simp] theorem sourceInput_targets
    (source : SourceSplitRouteDescriptorTokens.Source) :
    (sourceInput source).targets = SourceCycleLinkTargetIndices.targetIndices
      (SourceOccurrenceAtomGroupSizes.sizes source) := rfl

noncomputable def clauseCountComputableInPolyTime :
    TM2ComputableInPolyTime
      SourceSplitRouteDescriptorTokens.finEncoding.encode
      UnaryFieldEncoderMachine.unaryField
      (fun source : SourceSplitRouteDescriptorTokens.Source =>
        source.formula.clauses.length) :=
  TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    SourceClauseCountField.computableInPolyTime
    SourceClauseCountField.sourceField_eq

/-- The clause count, boundary tags, and aligned wrapped target indices are
prepared together in the tagged emitter's nested separated encoding. -/
noncomputable def sourceInputComputableInPolyTime :
    TM2ComputableInPolyTime
      SourceSplitRouteDescriptorTokens.finEncoding.encode encode sourceInput := by
  let header := TM2ForkMachine.computableInPolyTime
    clauseCountComputableInPolyTime
    SourceCycleLinkPositionTags.sourceTagsComputableInPolyTime
  let complete := TM2ForkMachine.computableInPolyTime header
    SourceCycleLinkTargetIndices.unaryFieldsComputableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq complete
    (fun _ => by rfl)

end LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitter

end
