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
import LeanTrominoes.UnarySuccessorEqualityFilterTime

/-! # Polynomial-time source last-occurrence contributions -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNF
namespace SourceOccurrenceAtomLastContributions

open Turing

local instance : Inhabited
    SourceSplitRouteDescriptorTokens.finEncoding.Γ :=
  ⟨PartrecToTM2.Γ'.bit0⟩

/-- Source atom-group sizes retained only at their final occurrence are
emitted as unary fields in polynomial time. -/
noncomputable def unaryFieldsComputableInPolyTime :
    TM2ComputableInPolyTime
      SourceSplitRouteDescriptorTokens.finEncoding.encode
      UnaryFieldEncoderMachine.unaryFields contributions := by
  let paired := TM2ForkMachine.computableInPolyTime
    SourceOccurrenceAtomRanks.unaryFieldsComputableInPolyTime
    SourceOccurrenceAtomPerOccurrenceGroupSizes.unaryFieldsComputableInPolyTime
  let prepared : TM2ComputableInPolyTime
      SourceSplitRouteDescriptorTokens.finEncoding.encode
      UnarySuccessorEqualityFilterMachine.encode filterInput :=
    TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq paired
      (fun source => by rfl)
  let filtered := TM2CompositionMachine.computableInPolyTime prepared
    UnarySuccessorEqualityFilterMachine.computableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq filtered
    (fun source => by rfl)

end SourceOccurrenceAtomLastContributions
end PeriodicCNF
end LeanTrominoes

end
