/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Source.PeriodicCNFSourceOccurrenceAtomPerOccurrenceBlockStartSemantics
import LeanTrominoes.SAT.CNF.Source.PeriodicCNFSourceOccurrenceAtomRotatedRankSemantics
import LeanTrominoes.Computation.TM2.TM2CompositionMachine
import LeanTrominoes.Computation.TM2.TM2ForkMachineTime
import LeanTrominoes.Computation.TM2.TM2PolyTimeOutputEncodingTransport
import LeanTrominoes.Computation.Encoding.Unary.UnaryAlignedAddTime
import LeanTrominoes.Computation.Encoding.Unary.UnaryAlignedAddValidity

/-! # Target vertex indices of source occurrence copies -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNF
namespace SourceOccurrenceTargetVertexIndices

open Turing

local instance : Inhabited
    SourceSplitRouteDescriptorTokens.finEncoding.Γ :=
  ⟨PartrecToTM2.Γ'.bit0⟩

def additionInput (source : SourceSplitRouteDescriptorTokens.Source) :
    UnaryAlignedAddMachine.Input where
  firsts := SourceOccurrenceAtomPerOccurrenceBlockStarts.starts source
  seconds := SourceOccurrenceAtomRotatedRanks.ranks source
  valid := UnaryAlignedAddMachine.Valid.of_length_eq (by
    rw [SourceOccurrenceAtomPerOccurrenceBlockStarts.starts_length,
      SourceOccurrenceAtomRotatedRanks.ranks_length])

def indices (source : SourceSplitRouteDescriptorTokens.Source) : List Nat :=
  UnaryAlignedAddMachine.sums
    (additionInput source).firsts (additionInput source).seconds

@[simp] theorem additionInput_firsts
    (source : SourceSplitRouteDescriptorTokens.Source) :
    (additionInput source).firsts =
      SourceOccurrenceAtomPerOccurrenceBlockStarts.starts source := rfl

@[simp] theorem additionInput_seconds
    (source : SourceSplitRouteDescriptorTokens.Source) :
    (additionInput source).seconds =
      SourceOccurrenceAtomRotatedRanks.ranks source := rfl

noncomputable def unaryFieldsComputableInPolyTime :
    TM2ComputableInPolyTime
      SourceSplitRouteDescriptorTokens.finEncoding.encode
      UnaryFieldEncoderMachine.unaryFields indices := by
  let paired := TM2ForkMachine.computableInPolyTime
    SourceOccurrenceAtomPerOccurrenceBlockStarts.unaryFieldsComputableInPolyTime
    SourceOccurrenceAtomRotatedRanks.unaryFieldsComputableInPolyTime
  let prepared : TM2ComputableInPolyTime
      SourceSplitRouteDescriptorTokens.finEncoding.encode
      UnaryAlignedAddMachine.encode additionInput :=
    TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq paired
      (fun _ => by rfl)
  let added := TM2CompositionMachine.computableInPolyTime prepared
    UnaryAlignedAddMachine.computableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq added
    (fun _ => by rfl)

end SourceOccurrenceTargetVertexIndices
end PeriodicCNF
end LeanTrominoes

end
