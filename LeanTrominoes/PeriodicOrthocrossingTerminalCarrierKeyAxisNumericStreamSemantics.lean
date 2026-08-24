/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyAxisStreamData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierKeyCandidateStreamData
import LeanTrominoes.PeriodicOrthocrossingTerminalCarrierKeyAxisNumericPairValueSemantics

/-! # Key-derived numeric terminal carrier-key axis stream -/

namespace LeanTrominoes.PeriodicOrthocrossing

open PaddedSupportedLastRepresentativeEqualityRows
open RouteDescriptorCarrierKeyAxisDatum

/-- The complete numeric terminal axis stream is the descriptor key-axis
datum mapped over the complete padded terminal candidate prefix. -/
theorem terminalCarrierKeyAxisValues_numeric_stream
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal) :
    CarrierKeyAxisStream.terminalValues
        (PeriodicCNF.numericRouteDescriptors formula) =
      (RouteDescriptorPairAffine.paddedTerminalCarrierKeyCandidateStream
        (PeriodicCNF.numericRouteDescriptors formula)).map
          (value (PeriodicCNF.numericRouteDescriptors formula) ∘
            Candidate.value) := by
  unfold CarrierKeyAxisStream.terminalValues
    RouteDescriptorPairAffine.paddedTerminalCarrierKeyCandidateStream
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro pair pairMember
  exact RouteDescriptorPairAffine.terminalCarrierKeyAxisValues_numeric_pair
    formula wellFormed degree isLocal pair pairMember

end LeanTrominoes.PeriodicOrthocrossing
