/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossingRecordSourceFieldDescriptorCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossingRecordSourceFieldPipelineSemantics
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Compiler for aligned source-key crossing-field values -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierCrossingRecordSourceField

open Computability Turing

noncomputable def alignedValuesWithSentinelComputableInPolyTime
    (field : Field) :
    TM2ComputableInPolyTime
      (fun descriptors : List RouteDescriptor =>
        DelimitedBinaryWords.encode
          (RouteDescriptorBinaryWords.words descriptors))
      UnaryFieldEncoderMachine.unaryFields
      (alignedValuesWithSentinel field) := by
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (CarrierCrossingRecordSourceFieldPipeline.descriptorFieldsComputableInPolyTime
      field)
    (CarrierCrossingRecordSourceFieldPipeline.fields_descriptorWords field)

end CarrierCrossingRecordSourceField
end LeanTrominoes.PeriodicOrthocrossing

end
