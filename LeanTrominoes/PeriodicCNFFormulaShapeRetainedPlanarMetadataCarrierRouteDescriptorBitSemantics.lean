/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorRetainedCarrierBitData
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierPairBitSemantics
import LeanTrominoes.PeriodicCNFIncidenceCrossingOccurrencePairEnumeration
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorCrossingPairs

/-! # Route-descriptor semantics of retained carrier-link bits -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- Numeric route descriptors determine each retained carrier key's exact
ordered representative-link axis and next-slice bit block. -/
theorem retainedCarrierLinkBitsAt_eq_routeDescriptorBits
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (key : Nat × Nat × Cell) :
    retainedCarrierLinkBitsAt source.incidenceGraph
        (carrierLinkNextSlice source) key =
      routeDescriptorRetainedCarrierPairBitsAtPeriod
        (drawingGridSize source.incidenceGraph)
        (numericRouteDescriptors source) key := by
  rw [retainedCarrierLinkBitsAt_eq_occurrencePairBits]
  unfold routeDescriptorRetainedCarrierPairBitsAtPeriod
    routeDescriptorRetainedCarrierNodesAtPeriod
  rw [incidenceGraph_neighborOccurrences_eq_numeric,
    numericNeighborOccurrences_eq_routeDescriptorNeighborOccurrences,
    incidenceGraph_orientedCrossingOccurrencePairs_eq_numeric,
    numericOrientedCrossingOccurrencePairs_eq_routeDescriptors]

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
