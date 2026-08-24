/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumLookupLength
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyRepresentativeLookupCompiler

/-! # Compiler interface for selected carrier rank fields -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankDatumLookup

open Computability Turing

/-- Any polynomial-time emitter for one aligned sentinel-completed rank field
composes with compact identity selection to compute that field over all
deduplicated representatives. -/
noncomputable def selectedFieldValuesComputableInPolyTime
    (period : List RouteDescriptor → Nat)
    (field : CarrierNodeRankDatum → Nat)
    (alignedFieldComputableInPolyTime :
      TM2ComputableInPolyTime
        (fun descriptors : List RouteDescriptor =>
          DelimitedBinaryWords.encode
            (RouteDescriptorBinaryWords.words descriptors))
        UnaryFieldEncoderMachine.unaryFields
        (fun descriptors => fieldValuesWithSentinelAtPeriod
          (period descriptors) descriptors field)) :
    TM2ComputableInPolyTime
      (fun descriptors : List RouteDescriptor =>
        DelimitedBinaryWords.encode
          (RouteDescriptorBinaryWords.words descriptors))
      UnaryFieldEncoderMachine.unaryFields
      (fun descriptors => selectedFieldValuesAtPeriod
        (period descriptors) descriptors field) :=
  CarrierSourceKeyRepresentativeLookup.valuesComputableInPolyTime
    (fun descriptors => fieldValuesWithSentinelAtPeriod
      (period descriptors) descriptors field)
    (fun descriptors => fieldValuesWithSentinelAtPeriod_length
      (period descriptors) descriptors field)
    alignedFieldComputableInPolyTime

end CarrierRankDatumLookup
end LeanTrominoes.PeriodicOrthocrossing

end
