/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierBoundaryPresenceDescriptorCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierBoundaryPresencePipelineSemantics
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Compiler for aligned carrier boundary-presence values -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierBoundaryPresenceField

open Computability Turing

noncomputable def alignedValuesWithSentinelComputableInPolyTime :
    TM2ComputableInPolyTime
      (fun descriptors : List RouteDescriptor =>
        DelimitedBinaryWords.encode
          (RouteDescriptorBinaryWords.words descriptors))
      UnaryFieldEncoderMachine.unaryFields
      alignedValuesWithSentinel := by
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    CarrierBoundaryPresencePipeline.descriptorFieldsComputableInPolyTime
    CarrierBoundaryPresencePipeline.fields_descriptorWords

end CarrierBoundaryPresenceField
end LeanTrominoes.PeriodicOrthocrossing

end
