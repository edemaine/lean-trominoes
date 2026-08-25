/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeyRouteFieldAlignedCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeyRouteFieldLength
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyRepresentativeLookupCompiler

/-! # Compiler for the selected carrier-key route field -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankKeyRouteField

open Computability Turing

/-- The route-index field of every deduplicated carrier-node representative
is emitted in unary in polynomial time. -/
noncomputable def valuesComputableInPolyTime :
    TM2ComputableInPolyTime
      (fun descriptors : List RouteDescriptor =>
        DelimitedBinaryWords.encode
          (RouteDescriptorBinaryWords.words descriptors))
      UnaryFieldEncoderMachine.unaryFields values :=
  CarrierSourceKeyRepresentativeLookup.valuesComputableInPolyTime
    alignedValuesWithSentinel
    alignedValuesWithSentinel_length_sourceKeyCandidates
    alignedValuesWithSentinelComputableInPolyTime

end CarrierRankKeyRouteField
end LeanTrominoes.PeriodicOrthocrossing

end
