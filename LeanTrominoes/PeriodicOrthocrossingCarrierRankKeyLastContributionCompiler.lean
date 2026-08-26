/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeyGroupSizeCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeyLastContribution
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeyOccurrenceRankCompiler
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2ForkMachineTime
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport
import LeanTrominoes.UnarySuccessorEqualityFilterTime

/-! # Compiler for last-occurrence carrier-key contributions -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankKeyLastContributions

open Turing

local instance : Inhabited DelimitedBinaryWords.finEncoding.Γ :=
  ⟨DelimitedBinaryWords.Token.wordStart⟩

opaque unaryFieldsComputableInPolyTime :
    TM2ComputableInPolyTime CarrierRankKeyEquality.InputEncoding
      UnaryFieldEncoderMachine.unaryFields contributions := by
  let paired := TM2ForkMachine.computableInPolyTime
    CarrierRankKeyOccurrenceRanks.unaryFieldsComputableInPolyTime
    CarrierRankKeyGroupSizes.unaryFieldsComputableInPolyTime
  let prepared : TM2ComputableInPolyTime
      CarrierRankKeyEquality.InputEncoding
      UnarySuccessorEqualityFilterMachine.encode filterInput :=
    TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq paired
      (fun descriptors => by
        simp only [UnarySuccessorEqualityFilterMachine.encode, filterInput])
  let filtered := TM2CompositionMachine.computableInPolyTime prepared
    UnarySuccessorEqualityFilterMachine.computableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq filtered
    (fun descriptors => by
      simp only [contributions, filterInput])

end CarrierRankKeyLastContributions
end LeanTrominoes.PeriodicOrthocrossing

end
