/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierKeyScanData
import LeanTrominoes.PeriodicCNFIncidenceCrossingOccurrencePairEnumerationData

/-! # Route-descriptor form of numeric retained carrier keys -/

namespace LeanTrominoes.PeriodicCNF

open PeriodicOrthocrossing

/-- Expanding the numeric occurrence-pair list is definitionally the retained
carrier-key scan over numeric route descriptors. -/
theorem numericRetainedCarrierKeyScan_eq_routeDescriptors
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    occurrencePairCarrierKeyScan
        (numericOrientedCrossingOccurrencePairs formula) =
      routeDescriptorRetainedCarrierKeyScanAtPeriod
        (drawingGridSize formula.incidenceGraph)
        (numericRouteDescriptors formula) := by
  rfl

end LeanTrominoes.PeriodicCNF
