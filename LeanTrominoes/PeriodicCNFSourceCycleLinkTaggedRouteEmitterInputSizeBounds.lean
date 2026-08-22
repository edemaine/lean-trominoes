/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterParseToScanExecution

/-! # Encoded-input size bounds for tagged cycle-link route emission -/

namespace LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine

@[simp] theorem encode_length
    (input : SourceCycleLinkTaggedRouteEmitter.Input) :
    (SourceCycleLinkTaggedRouteEmitter.encode input).length =
      input.clauseCount + input.literalCount +
        (UnaryFieldEncoderMachine.unaryFields input.targets).length + 3 := by
  simp [SourceCycleLinkTaggedRouteEmitter.encode,
    SourceCycleLinkTaggedRouteEmitter.Input.literalCount,
    SeparatedProductEncoding.encode,
    UnaryFieldEncoderMachine.unaryField_length]
  omega

theorem one_le_encode_length
    (input : SourceCycleLinkTaggedRouteEmitter.Input) :
    1 ≤ (SourceCycleLinkTaggedRouteEmitter.encode input).length := by
  rw [encode_length]
  omega

theorem clauseCount_le_encode_length
    (input : SourceCycleLinkTaggedRouteEmitter.Input) :
    input.clauseCount ≤
      (SourceCycleLinkTaggedRouteEmitter.encode input).length := by
  rw [encode_length]
  omega

theorem literalCount_add_one_le_encode_length
    (input : SourceCycleLinkTaggedRouteEmitter.Input) :
    input.literalCount + 1 ≤
      (SourceCycleLinkTaggedRouteEmitter.encode input).length := by
  rw [encode_length]
  omega

theorem unaryTargets_length_le_encode_length
    (input : SourceCycleLinkTaggedRouteEmitter.Input) :
    (UnaryFieldEncoderMachine.unaryFields input.targets).length ≤
      (SourceCycleLinkTaggedRouteEmitter.encode input).length := by
  rw [encode_length]
  omega

theorem target_le_unaryFields_cons_length
    (target : Nat) (targets : List Nat) :
    target ≤
      (UnaryFieldEncoderMachine.unaryFields (target :: targets)).length := by
  simp only [UnaryFieldEncoderMachine.unaryFields_cons,
    List.length_append, UnaryFieldEncoderMachine.unaryField_length]
  omega

theorem parseTime_le_four_encode_length
    (input : SourceCycleLinkTaggedRouteEmitter.Input) :
    parseTime input.clauseCount input.tags
        (UnaryFieldEncoderMachine.unaryFields input.targets) ≤
      4 * (SourceCycleLinkTaggedRouteEmitter.encode input).length := by
  rw [encode_length]
  simp only [parseTime,
    SourceCycleLinkTaggedRouteEmitter.Input.literalCount]
  omega

end LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine
