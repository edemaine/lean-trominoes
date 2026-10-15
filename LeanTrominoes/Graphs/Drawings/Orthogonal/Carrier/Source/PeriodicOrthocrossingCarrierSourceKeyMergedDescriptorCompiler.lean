/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.Graphs.Drawings.Orthogonal.Carrier.Source.PeriodicOrthocrossingCarrierSourceKeyMergedCandidateSemantics
import LeanTrominoes.Graphs.Drawings.Orthogonal.Carrier.Source.PeriodicOrthocrossingCarrierSourceKeyMergedDescriptorOutputData
import LeanTrominoes.Graphs.Drawings.Orthogonal.Carrier.Source.PeriodicOrthocrossingCarrierSourceKeyMergedStreamCompiler
import LeanTrominoes.Computation.TM2.TM2PolyTimeOutputEncodingTransport

/-! # Descriptor-list compiler for merged carrier source-key words -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierSourceKeyMergedStream

open Computability Turing

noncomputable def descriptorOutputComputableInPolyTime :
    TM2ComputableInPolyTime
      (fun descriptors : List RouteDescriptor =>
        DelimitedBinaryWords.encode
          (RouteDescriptorBinaryWords.words descriptors))
      DelimitedBinaryWords.finEncoding.encode descriptorOutput := by
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    descriptorTokensComputableInPolyTime
    (fun descriptors => by
      exact tokens_descriptorWords descriptors)

end CarrierSourceKeyMergedStream
end LeanTrominoes.PeriodicOrthocrossing

end
