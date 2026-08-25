/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierActiveKeyRouteFieldProjectionCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorBinaryWordData
import LeanTrominoes.TM2PolyTimeInputEncodingTransport

/-! # Descriptor-input compiler for active carrier-key route projection -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierActiveKeyRouteFieldProjection

open Computability Turing

/-- Reinterpret physical route projection at the canonical descriptor-list
input boundary. -/
noncomputable def descriptorOutputComputableInPolyTime :
    TM2ComputableInPolyTime
      (fun descriptors : List RouteDescriptor =>
        DelimitedBinaryWords.encode
          (RouteDescriptorBinaryWords.words descriptors))
      id
      (fun descriptors => CarrierKeyRouteFieldProjector.output
        (CarrierActiveKeyRecipeStream.emittedTokens
          (RouteDescriptorBinaryWords.words descriptors))) := by
  exact TM2PolyTimeInputEncodingTransport.of_prepare
    RouteDescriptorBinaryWords.words physicalOutputComputableInPolyTime
    (fun _ => rfl) (fun _ => rfl)

end CarrierActiveKeyRouteFieldProjection
end LeanTrominoes.PeriodicOrthocrossing

end
