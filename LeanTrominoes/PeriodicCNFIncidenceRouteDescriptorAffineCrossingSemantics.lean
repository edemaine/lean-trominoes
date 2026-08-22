/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorLocalShape
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorSelfIndex
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineCrossingBlockSemantics

/-! # Exact affine crossing scans for forward-local CNF descriptors -/

namespace LeanTrominoes
namespace PeriodicCNF

open PeriodicOrthocrossing
open PeriodicOrthocrossing.RouteDescriptorPairAffine

/-- The finite affine evaluator on a nonempty forward-local CNF descriptor
stream emits exactly thirteen markers per canonical oriented crossing. -/
theorem numericRouteDescriptors_affineCrossingMarkerStream_eq_replicate
    {Variable : Type*} [DecidableEq Variable]
    (marker : α) (formula : PeriodicCNF Variable)
    (forward : formula.IsForwardLocal)
    (nonempty : incidencesWithMetadata formula ≠ []) :
    affineCrossingMarkerStream marker (numericRouteDescriptors formula) =
      List.replicate
        (13 * routeDescriptorOrientedCrossingCount
          (numericRouteDescriptors formula)) marker := by
  exact affineCrossingMarkerStream_eq_replicate marker
    (numericRouteDescriptors formula)
    (numericRouteDescriptors_all_hasLocalShape formula forward)
    (numericRouteDescriptors_selfIndexed formula)
    (numericRouteDescriptors_commonGridSize formula nonempty)

end PeriodicCNF
end LeanTrominoes
