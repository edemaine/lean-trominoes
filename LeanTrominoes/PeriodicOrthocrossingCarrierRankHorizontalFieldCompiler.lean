/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyAxisSentinelCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyAxisSourceKeyAlignment
import LeanTrominoes.PeriodicOrthocrossingCarrierRankHorizontalFieldData
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyRepresentativeLookupCompiler

/-! # Compiler for the selected carrier horizontal field -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankHorizontalField

open Computability Turing

/-- The horizontal field of every deduplicated carrier-node representative
is emitted in unary in polynomial time. -/
noncomputable def valuesComputableInPolyTime :
    TM2ComputableInPolyTime
      (fun descriptors : List RouteDescriptor =>
        DelimitedBinaryWords.encode
          (RouteDescriptorBinaryWords.words descriptors))
      UnaryFieldEncoderMachine.unaryFields values :=
  CarrierSourceKeyRepresentativeLookup.valuesComputableInPolyTime
    CarrierKeyAxisStream.valuesWithSentinel
    CarrierKeyAxisStream.valuesWithSentinel_length_sourceKeyCandidates
    paddedCarrierKeyAxisValuesWithSentinelComputableInPolyTime

end CarrierRankHorizontalField
end LeanTrominoes.PeriodicOrthocrossing

end
