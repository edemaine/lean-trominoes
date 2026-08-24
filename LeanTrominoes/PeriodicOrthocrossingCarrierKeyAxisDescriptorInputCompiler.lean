/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyAxisPipelineCompiler
import LeanTrominoes.TM2PolyTimeInputEncodingTransport

/-! # Carrier-key axis compiler at the descriptor-list input boundary -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyAxisPipeline

open Computability Turing

/-- Reinterpret the physical pipeline on canonical descriptor words while
retaining its physical unary-field output. -/
noncomputable def descriptorFieldsComputableInPolyTime :
    TM2ComputableInPolyTime
      (fun descriptors : List RouteDescriptor =>
        DelimitedBinaryWords.encode
          (RouteDescriptorBinaryWords.words descriptors))
      id
      (fun descriptors =>
        fields (RouteDescriptorBinaryWords.words descriptors)) := by
  exact TM2PolyTimeInputEncodingTransport.of_prepare
    RouteDescriptorBinaryWords.words fieldsComputableInPolyTime
    (fun _ => rfl) (fun _ => rfl)

end CarrierKeyAxisPipeline
end LeanTrominoes.PeriodicOrthocrossing

end
