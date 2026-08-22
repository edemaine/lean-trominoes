/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairDelimiterData

/-! # Body preceding a route-descriptor pair delimiter -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairFieldTags

def descriptorPairBody
    (pair : RouteDescriptor × RouteDescriptor) : List Token :=
  .pairStart ::
    (descriptorUnits .first pair.1 ++ descriptorUnits .second pair.2)

end RouteDescriptorPairFieldTags
end PeriodicOrthocrossing
end LeanTrominoes
