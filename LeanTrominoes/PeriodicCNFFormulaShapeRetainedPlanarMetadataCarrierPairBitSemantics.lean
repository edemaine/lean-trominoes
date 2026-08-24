/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairRetainedCarrierBitData
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairRetainedCarrierRepresentativeSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierPairNextSliceSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierLinkBitKeySemantics

/-! # Exact occurrence-pair semantics of retained carrier-link bits -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- For one physical carrier key, the reconstructed occurrence-pair scan
emits exactly the semantic representative links' axis and next-slice bits in
their established order. -/
theorem retainedCarrierLinkBitsAt_eq_occurrencePairBits
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (key : Nat × Nat × Cell) :
    retainedCarrierLinkBitsAt source.incidenceGraph
        (carrierLinkNextSlice source) key =
      retainedRepresentativeCarrierPairBitsAtPeriod
        (drawingGridSize source.incidenceGraph)
        (retainedCarrierNodesOfOccurrencesAndPairsAtPeriod
          (drawingGridSize source.incidenceGraph)
          (neighborOccurrences source.incidenceGraph)
          (orientedCrossingOccurrencePairs source.incidenceGraph)) key := by
  unfold retainedCarrierLinkBitsAt
    retainedRepresentativeCarrierPairBitsAtPeriod
  rw [retainedRepresentativeCarrierLinksAt_eq_nodePairsAtPeriod,
    List.map_map]
  apply List.map_congr_left
  intro pair pairMember
  apply Prod.ext
  · rfl
  · exact
      (carrierNodePairNextSliceAtPeriod_eq_carrierLinkNextSlice
        source pair).symm

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
