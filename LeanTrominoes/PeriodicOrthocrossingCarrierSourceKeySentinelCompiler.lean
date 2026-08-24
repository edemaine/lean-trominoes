/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyCompiledSentinelSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyMergedStreamCompiler
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Compiler for sentinel-completed carrier source-key words -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing

open Computability Turing
open PaddedSupportedCandidateWords

noncomputable def paddedCarrierSourceKeyWordsWithSentinelComputableInPolyTime :
    TM2ComputableInPolyTime
      (fun descriptors : List RouteDescriptor =>
        DelimitedBinaryWords.encode
          (RouteDescriptorBinaryWords.words descriptors))
      DelimitedBinaryWords.finEncoding.encode
      paddedCarrierSourceKeyWordsWithSentinel := by
  let appended := TM2CompositionMachine.computableInPolyTime
    CarrierSourceKeyMergedStream.descriptorTokensComputableInPolyTime
    (TM2ListAppend.appendFixedComputableInPolyTime
      (DelimitedBinaryWords.wordTokens sentinelWord))
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq appended
    appendedCompiledSourceKeySentinelTokens_eq

end LeanTrominoes.PeriodicOrthocrossing

end
