/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierBoundaryPresencePipelineCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorBinaryWordData
import LeanTrominoes.TM2PolyTimeInputEncodingTransport

/-! # Descriptor-input compiler for carrier boundary presence -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierBoundaryPresencePipeline

open Computability Turing

noncomputable def descriptorFieldsComputableInPolyTime :
    TM2ComputableInPolyTime
      (fun descriptors : List RouteDescriptor =>
        DelimitedBinaryWords.encode
          (RouteDescriptorBinaryWords.words descriptors))
      id
      (fun descriptors => fields
        (RouteDescriptorBinaryWords.words descriptors)) := by
  exact TM2PolyTimeInputEncodingTransport.of_prepare
    RouteDescriptorBinaryWords.words fieldsComputableInPolyTime
    (fun _ => rfl) (fun _ => rfl)

end CarrierBoundaryPresencePipeline
end LeanTrominoes.PeriodicOrthocrossing

end
