/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceAtomLastContribution
import LeanTrominoes.PeriodicCNFSourceOccurrenceAtomPerOccurrenceGroupSizeCompiler
import LeanTrominoes.PeriodicCNFSourceOccurrenceAtomRankCompiler
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2ForkMachineTime
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport
import LeanTrominoes.UnaryRotatedRanksTime

/-! # Rotated local ranks of source atom occurrences -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNF
namespace SourceOccurrenceAtomRotatedRanks

open Turing

local instance : Inhabited
    SourceSplitRouteDescriptorTokens.finEncoding.Γ :=
  ⟨PartrecToTM2.Γ'.bit0⟩

def rotationInput (source : SourceSplitRouteDescriptorTokens.Source) :
    UnaryRotatedRanksMachine.Input where
  ranks := SourceOccurrenceAtomRanks.ranks source
  sizes := SourceOccurrenceAtomPerOccurrenceGroupSizes.sizes source
  valid := (SourceOccurrenceAtomLastContributions.filterInput source).valid

def ranks (source : SourceSplitRouteDescriptorTokens.Source) : List Nat :=
  UnaryRotatedRanksMachine.rotatedRanks
    (rotationInput source).ranks (rotationInput source).sizes

@[simp] theorem rotationInput_ranks
    (source : SourceSplitRouteDescriptorTokens.Source) :
    (rotationInput source).ranks = SourceOccurrenceAtomRanks.ranks source := rfl

@[simp] theorem rotationInput_sizes
    (source : SourceSplitRouteDescriptorTokens.Source) :
    (rotationInput source).sizes =
      SourceOccurrenceAtomPerOccurrenceGroupSizes.sizes source := rfl

noncomputable def unaryFieldsComputableInPolyTime :
    TM2ComputableInPolyTime
      SourceSplitRouteDescriptorTokens.finEncoding.encode
      UnaryFieldEncoderMachine.unaryFields ranks := by
  let paired := TM2ForkMachine.computableInPolyTime
    SourceOccurrenceAtomRanks.unaryFieldsComputableInPolyTime
    SourceOccurrenceAtomPerOccurrenceGroupSizes.unaryFieldsComputableInPolyTime
  let prepared : TM2ComputableInPolyTime
      SourceSplitRouteDescriptorTokens.finEncoding.encode
      UnaryRotatedRanksMachine.encode rotationInput :=
    TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq paired
      (fun _ => by rfl)
  let rotated := TM2CompositionMachine.computableInPolyTime prepared
    UnaryRotatedRanksMachine.computableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq rotated
    (fun _ => by rfl)

end SourceOccurrenceAtomRotatedRanks
end PeriodicCNF
end LeanTrominoes

end
