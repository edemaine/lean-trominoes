/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorLocalShape
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorSelfIndex
import LeanTrominoes.PeriodicOrthocrossingCrossingCarrierKeyAxisStreamKeySemantics

/-! # Key-derived numeric crossing carrier-key axis stream -/

namespace LeanTrominoes.PeriodicOrthocrossing

open PaddedSupportedLastRepresentativeEqualityRows
open RouteDescriptorOccurrenceSlotBinaryWords
open RouteDescriptorOccurrenceSlotPairFieldTags
open RouteDescriptorOccurrenceSlotCrossing

/-- The complete numeric crossing axis stream is the descriptor key-axis
datum mapped over the complete padded crossing candidate suffix. -/
theorem crossingCarrierKeyAxisValues_numeric_tagged_stream
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (forward : formula.IsForwardLocal) :
    (taggedDescriptors (PeriodicCNF.numericRouteDescriptors formula) ×ˢ
        taggedDescriptors
          (PeriodicCNF.numericRouteDescriptors formula)).flatMap (fun pair =>
      crossingCarrierKeyAxisValues (descriptorSlotPairTokens pair)) =
      (paddedCrossingCarrierKeyCandidateStream
          (PeriodicCNF.numericRouteDescriptors formula)).map
        (RouteDescriptorCarrierKeyAxisDatum.value
            (PeriodicCNF.numericRouteDescriptors formula) ∘
          Candidate.value) := by
  exact crossingCarrierKeyAxisValues_stream_eq_map_candidates
      (PeriodicCNF.numericRouteDescriptors formula)
      (PeriodicCNF.numericRouteDescriptors_selfIndexed formula)
      (PeriodicCNF.numericRouteDescriptors_all_hasLocalShape
        formula forward)

end LeanTrominoes.PeriodicOrthocrossing
