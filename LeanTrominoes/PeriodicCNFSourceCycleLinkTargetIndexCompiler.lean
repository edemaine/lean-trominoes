/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkTargetIndexRotationSemantics
import LeanTrominoes.PeriodicCNFSourceOccurrenceAtomBlockStartCompiler
import LeanTrominoes.PeriodicCNFSourceOccurrenceAtomGroupSizeCompiler
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2ForkMachineTime
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport
import LeanTrominoes.UnaryBlockRightRotationTime

/-! # Polynomial-time source cycle-link target indices -/

noncomputable section

namespace LeanTrominoes.PeriodicCNF.SourceCycleLinkTargetIndices

open Turing

local instance : Inhabited
    SourceSplitRouteDescriptorTokens.finEncoding.Γ :=
  ⟨PartrecToTM2.Γ'.bit0⟩

def rotationInput (source : SourceSplitRouteDescriptorTokens.Source) :
    UnaryBlockRightRotationMachine.Input where
  groupSizes := SourceOccurrenceAtomGroupSizes.sizes source
  blockStarts := SourceOccurrenceAtomBlockStarts.starts source
  valid := by
    unfold SourceOccurrenceAtomBlockStarts.starts
    exact UnaryBlockRightRotationMachine.Valid.prefixStarts _

@[simp] theorem rotationInput_groupSizes
    (source : SourceSplitRouteDescriptorTokens.Source) :
    (rotationInput source).groupSizes =
      SourceOccurrenceAtomGroupSizes.sizes source := rfl

@[simp] theorem rotationInput_blockStarts
    (source : SourceSplitRouteDescriptorTokens.Source) :
    (rotationInput source).blockStarts =
      SourceOccurrenceAtomBlockStarts.starts source := rfl

theorem rotationOutput_eq
    (source : SourceSplitRouteDescriptorTokens.Source) :
    UnaryBlockRightRotationMachine.rotatedBlocks
        (rotationInput source).groupSizes
        (rotationInput source).blockStarts =
      targetIndices (SourceOccurrenceAtomGroupSizes.sizes source) := by
  simpa [rotationInput, SourceOccurrenceAtomBlockStarts.starts] using
    rotatedBlocks_prefixStarts
      (SourceOccurrenceAtomGroupSizes.sizes source)

/-- The source-variable index targeted by every negative cycle link is
emitted as a unary field in polynomial time. -/
noncomputable def unaryFieldsComputableInPolyTime :
    TM2ComputableInPolyTime
      SourceSplitRouteDescriptorTokens.finEncoding.encode
      UnaryFieldEncoderMachine.unaryFields
      (fun source =>
        targetIndices (SourceOccurrenceAtomGroupSizes.sizes source)) := by
  let paired := TM2ForkMachine.computableInPolyTime
    SourceOccurrenceAtomGroupSizes.unaryFieldsComputableInPolyTime
    SourceOccurrenceAtomBlockStarts.unaryFieldsComputableInPolyTime
  let prepared : TM2ComputableInPolyTime
      SourceSplitRouteDescriptorTokens.finEncoding.encode
      UnaryBlockRightRotationMachine.encode rotationInput :=
    TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq paired
      (fun _ => by rfl)
  let rotated := TM2CompositionMachine.computableInPolyTime prepared
    UnaryBlockRightRotationMachine.computableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq rotated
    (fun source => by rw [rotationOutput_eq source])

end LeanTrominoes.PeriodicCNF.SourceCycleLinkTargetIndices

end
