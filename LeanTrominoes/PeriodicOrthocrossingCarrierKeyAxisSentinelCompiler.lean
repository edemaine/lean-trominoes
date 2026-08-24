/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyAxisDescriptorInputCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyAxisSentinelSemantics
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2ListAppendFixedCompiler
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Polynomial-time sentinel-completed carrier-key axis stream -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing

open Computability Turing

/-- From canonical route-descriptor words, emit one unary axis field for
every padded carrier-key candidate followed by the unary-zero rejection
sentinel. -/
noncomputable def paddedCarrierKeyAxisValuesWithSentinelComputableInPolyTime :
    TM2ComputableInPolyTime
      (fun descriptors : List RouteDescriptor =>
        DelimitedBinaryWords.encode
          (RouteDescriptorBinaryWords.words descriptors))
      UnaryFieldEncoderMachine.unaryFields
      CarrierKeyAxisStream.valuesWithSentinel := by
  let appended := TM2CompositionMachine.computableInPolyTime
    CarrierKeyAxisPipeline.descriptorFieldsComputableInPolyTime
    (TM2ListAppend.appendFixedComputableInPolyTime
      [UnaryFieldEncoderMachine.Symbol.delimiter])
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq appended
    (fun descriptors => by
      unfold TM2ListAppend.appendFixedWords
      exact CarrierKeyAxisPipeline.fields_appendSentinel_descriptorWords
        descriptors)

end LeanTrominoes.PeriodicOrthocrossing

end
