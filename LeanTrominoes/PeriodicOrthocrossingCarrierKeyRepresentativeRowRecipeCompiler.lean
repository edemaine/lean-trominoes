/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeStreamSentinelSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierKeyRepresentativeRowCompiler
import LeanTrominoes.TM2PolyTimeInputEncodingTransport

/-! # Carrier-key representative rows from compiled recipe streams -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing

open Computability Turing

/-- The complete compiled recipe stream, viewed at the canonical descriptor
list boundary, emits exactly the guarded padded candidates plus sentinel. -/
noncomputable def paddedCarrierKeyWordsWithSentinelComputableInPolyTime :
    TM2ComputableInPolyTime
      (fun descriptors : List RouteDescriptor =>
        DelimitedBinaryWords.encode
          (RouteDescriptorBinaryWords.words descriptors))
      DelimitedBinaryWords.finEncoding.encode
      paddedCarrierKeyWordsWithSentinel := by
  exact TM2PolyTimeInputEncodingTransport.of_prepare
    RouteDescriptorBinaryWords.words
    CarrierKeyRecipeStream.outputWithSentinelComputableInPolyTime
    (fun _ => rfl)
    CarrierKeyRecipeStream.outputWithSentinel_descriptorWords

/-- The recipe emitter followed by the generic representative pipeline
computes the established sentinel-free carrier-key representative rows. -/
noncomputable def paddedCarrierKeyRepresentativeRowsRecipeComputableInPolyTime :
    TM2ComputableInPolyTime
      (fun descriptors : List RouteDescriptor =>
        DelimitedBinaryWords.encode
          (RouteDescriptorBinaryWords.words descriptors))
      DelimitedBinaryWords.finEncoding.encode
      paddedCarrierKeyRepresentativeRows := by
  exact paddedCarrierKeyRepresentativeRowsComputableInPolyTime
    (fun descriptors => DelimitedBinaryWords.encode
      (RouteDescriptorBinaryWords.words descriptors))
    paddedCarrierKeyWordsWithSentinelComputableInPolyTime

end LeanTrominoes.PeriodicOrthocrossing

end
