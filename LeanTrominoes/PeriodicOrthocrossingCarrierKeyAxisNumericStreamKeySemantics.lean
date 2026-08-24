/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyAxisNumericCrossingStreamSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierKeyCandidateStreamData
import LeanTrominoes.PeriodicOrthocrossingTerminalCarrierKeyAxisNumericStreamSemantics

/-! # Key-derived complete numeric carrier-key axis stream -/

namespace LeanTrominoes.PeriodicOrthocrossing

open PaddedSupportedLastRepresentativeEqualityRows

/-- The complete numeric terminal-prefix/crossing-suffix axis stream is the
descriptor key-axis datum mapped over the complete padded candidate stream. -/
theorem carrierKeyAxisValues_numeric_stream
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal) :
    CarrierKeyAxisStream.values
        (PeriodicCNF.numericRouteDescriptors formula) =
      (values (paddedCarrierKeyCandidateStream
        (PeriodicCNF.numericRouteDescriptors formula))).map
          (RouteDescriptorCarrierKeyAxisDatum.value
            (PeriodicCNF.numericRouteDescriptors formula)) := by
  unfold CarrierKeyAxisStream.values
  rw [terminalCarrierKeyAxisValues_numeric_stream
    formula wellFormed degree isLocal]
  rw [crossingCarrierKeyAxisValues_numeric_stream formula forward]
  simp [paddedCarrierKeyCandidateStream, values,
    List.map_append, List.map_map, Function.comp_def]

end LeanTrominoes.PeriodicOrthocrossing
