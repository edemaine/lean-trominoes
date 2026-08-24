/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyAxisStreamData
import LeanTrominoes.PeriodicOrthocrossingCrossingCarrierKeyAxisNumericStreamSemantics

/-! # Public key-derived numeric crossing axis stream -/

namespace LeanTrominoes.PeriodicOrthocrossing

open PaddedSupportedLastRepresentativeEqualityRows
open RouteDescriptorOccurrenceSlotCrossing

/-- The complete numeric crossing axis stream is the descriptor key-axis
datum mapped over the complete padded crossing candidate suffix. -/
theorem crossingCarrierKeyAxisValues_numeric_stream
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (forward : formula.IsForwardLocal) :
    CarrierKeyAxisStream.crossingValues
        (PeriodicCNF.numericRouteDescriptors formula) =
      (paddedCrossingCarrierKeyCandidateStream
          (PeriodicCNF.numericRouteDescriptors formula)).map
        (RouteDescriptorCarrierKeyAxisDatum.value
            (PeriodicCNF.numericRouteDescriptors formula) ∘
          Candidate.value) := by
  unfold CarrierKeyAxisStream.crossingValues
  exact crossingCarrierKeyAxisValues_numeric_tagged_stream formula forward

end LeanTrominoes.PeriodicOrthocrossing
