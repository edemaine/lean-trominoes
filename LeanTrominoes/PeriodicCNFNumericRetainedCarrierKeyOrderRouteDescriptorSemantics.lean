/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierKeyOrderData
import LeanTrominoes.PeriodicCNFIncidenceCrossingOccurrencePairEnumerationData

/-! # Route-descriptor form of numeric retained carrier-key order -/

namespace LeanTrominoes.PeriodicCNF

open PeriodicOrthocrossing

/-- Applying the graph-free retained-key ordering function to the numeric
incidence streams is definitionally its route-descriptor instantiation. -/
theorem numericRetainedCarrierKeys_eq_routeDescriptors
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    retainedCarrierKeysOfOccurrencesAndPairs
        (numericNeighborOccurrences formula)
        (numericOrientedCrossingOccurrencePairs formula) =
      routeDescriptorRetainedCarrierKeysAtPeriod
        (drawingGridSize formula.incidenceGraph)
        (numericRouteDescriptors formula) := by
  rfl

end LeanTrominoes.PeriodicCNF
