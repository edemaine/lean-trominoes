/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyAxisDescriptorInputCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyAxisPipelineSemantics
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Polynomial-time complete padded carrier-key axis stream -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing

open Computability Turing

/-- From canonical route-descriptor words, emit one canonical unary zero-or-
one axis field for every padded terminal or crossing carrier-key candidate. -/
noncomputable def paddedCarrierKeyAxisValuesComputableInPolyTime :
    TM2ComputableInPolyTime
      (fun descriptors : List RouteDescriptor =>
        DelimitedBinaryWords.encode
          (RouteDescriptorBinaryWords.words descriptors))
      UnaryFieldEncoderMachine.unaryFields
      CarrierKeyAxisStream.values := by
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    CarrierKeyAxisPipeline.descriptorFieldsComputableInPolyTime
    CarrierKeyAxisPipeline.fields_descriptorWords

end LeanTrominoes.PeriodicOrthocrossing

end
