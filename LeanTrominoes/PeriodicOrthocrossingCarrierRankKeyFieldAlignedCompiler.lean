/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierActiveKeyFieldDescriptorCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierActiveKeyFieldProjectionSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeyFieldData
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Compiler for padded aligned carrier-key fields -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankKeyField

open Computability Turing

/-- Emit any semantically verified key column at every padded carrier node,
followed by the unary-zero representative-lookup sentinel. -/
noncomputable def alignedValuesWithSentinelComputableInPolyTime
    (field : CarrierKeyFieldProjector.Field)
    (wordCorrect : CarrierKeyFieldProjector.WordCorrect field) :
    TM2ComputableInPolyTime
      (fun descriptors : List RouteDescriptor =>
        DelimitedBinaryWords.encode
          (RouteDescriptorBinaryWords.words descriptors))
      UnaryFieldEncoderMachine.unaryFields
      (alignedValuesWithSentinel field) := by
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (CarrierActiveKeyFieldProjection.descriptorOutputComputableInPolyTime
      field)
    (CarrierActiveKeyRecipeStream.keyFieldOutput_descriptorWords
      field wordCorrect)

end CarrierRankKeyField
end LeanTrominoes.PeriodicOrthocrossing

end
