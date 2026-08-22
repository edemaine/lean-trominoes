/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairFieldTags

/-! # Final-delimiter data of canonical route-descriptor pairs -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairFieldTags

def isPairEnd : Token → Bool
  | .pairEnd => true
  | _ => false

end RouteDescriptorPairFieldTags
end PeriodicOrthocrossing
end LeanTrominoes
