/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFallbackSourcePrefixDirectionData
import LeanTrominoes.RetainedAngularTerminalDataProfile

/-! # Scaled-route evidence data for final retained carriers -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicOrthocrossing

/-- The four source-side facts consumed by final-carrier directional
extensionality, parameterized by the already-expanded route data so Lean does
not repeatedly normalize the final reduction's large route expression. -/
structure FinalCarrierScaledRouteEvidence
    (route : List Cell)
    (terminalData : RetainedTerminalData)
    (prefixDirections : List AxisDirection) : Prop where
  routeLength :
    2 ≤ route.length
  routeClassified :
    retainedTerminalDirectionClassify
        (PeriodicThreeSATThree.routeTerminalVector route) =
      some terminalData
  routeOrthogonal :
    OrthogonalPolyline route
  routePrefixDirections :
    Gadget.unitSubdivisionDirections
        (retainedFallbackSourcePrefix route) =
      prefixDirections

end PeriodicEightOccurrenceSplit
end LeanTrominoes
