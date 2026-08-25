/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossingRecordSourceFieldPipelineCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorBinaryWordData
import LeanTrominoes.TM2PolyTimeInputEncodingTransport

/-! # Descriptor-input compiler for source-key crossing fields -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierCrossingRecordSourceFieldPipeline

open Computability Turing

noncomputable def descriptorFieldsComputableInPolyTime
    (field : CarrierCrossingRecordSourceField.Field) :
    TM2ComputableInPolyTime
      (fun descriptors : List RouteDescriptor =>
        DelimitedBinaryWords.encode
          (RouteDescriptorBinaryWords.words descriptors))
      id
      (fun descriptors => fields field
        (RouteDescriptorBinaryWords.words descriptors)) := by
  exact TM2PolyTimeInputEncodingTransport.of_prepare
    RouteDescriptorBinaryWords.words (fieldsComputableInPolyTime field)
    (fun _ => rfl) (fun _ => rfl)

end CarrierCrossingRecordSourceFieldPipeline
end LeanTrominoes.PeriodicOrthocrossing

end
