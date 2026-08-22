/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorScanTokenDecoderSemantics

/-! # Finite encoding by normalized route-descriptor scan tokens -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorScanTokens

/-- The verified normalized token format as a finite encoding of descriptor
lists. -/
noncomputable def finEncoding :
    _root_.Computability.FinEncoding (List RouteDescriptor) where
  toEncoding :=
    { Γ := Token
      encode := encode
      decode := decode
      decode_encode := decode_encode }
  ΓFin := inferInstance

end RouteDescriptorScanTokens
end PeriodicOrthocrossing
end LeanTrominoes

end
