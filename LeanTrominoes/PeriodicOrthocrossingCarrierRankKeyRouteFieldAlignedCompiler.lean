/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierActiveKeyRouteFieldDescriptorCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeyRouteFieldAlignedSemantics
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Compiler for padded aligned carrier-key route fields -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankKeyRouteField

open Computability Turing

/-- Emit one unary route-index value per padded carrier node followed by
the unary-zero representative-lookup sentinel. -/
noncomputable def alignedValuesWithSentinelComputableInPolyTime :
    TM2ComputableInPolyTime
      (fun descriptors : List RouteDescriptor =>
        DelimitedBinaryWords.encode
          (RouteDescriptorBinaryWords.words descriptors))
      UnaryFieldEncoderMachine.unaryFields
      alignedValuesWithSentinel := by
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    CarrierActiveKeyRouteFieldProjection.descriptorOutputComputableInPolyTime
    output_emittedTokens_descriptorWords

end CarrierRankKeyRouteField
end LeanTrominoes.PeriodicOrthocrossing

end
