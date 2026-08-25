/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierActiveKeyFieldProjectionCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorBinaryWordData
import LeanTrominoes.TM2PolyTimeInputEncodingTransport

/-! # Descriptor-input compiler for generic carrier-key fields -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierActiveKeyFieldProjection

open Computability Turing

/-- Reinterpret one physical key-column projection at the canonical
descriptor-list input boundary. -/
noncomputable def descriptorOutputComputableInPolyTime
    (field : CarrierKeyFieldProjector.Field) :
    TM2ComputableInPolyTime
      (fun descriptors : List RouteDescriptor =>
        DelimitedBinaryWords.encode
          (RouteDescriptorBinaryWords.words descriptors))
      id
      (fun descriptors => CarrierKeyFieldProjector.output field
        (CarrierActiveKeyRecipeStream.emittedTokens
          (RouteDescriptorBinaryWords.words descriptors))) := by
  exact TM2PolyTimeInputEncodingTransport.of_prepare
    RouteDescriptorBinaryWords.words
    (physicalOutputComputableInPolyTime field)
    (fun _ => rfl) (fun _ => rfl)

end CarrierActiveKeyFieldProjection
end LeanTrominoes.PeriodicOrthocrossing

end
