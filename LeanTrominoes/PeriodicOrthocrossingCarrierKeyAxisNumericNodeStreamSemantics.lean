/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateValueMapSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyAxisNumericStreamKeySemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeKeyCandidateStreamSemantics

/-! # Numeric carrier-key axes aligned with padded carrier nodes -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing

open PaddedSupportedLastRepresentativeEqualityRows

/-- The numeric carrier-key axis stream can be viewed pointwise over the
underlying padded carrier-node stream. -/
theorem carrierKeyAxisValues_numeric_nodeStream
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal) :
    CarrierKeyAxisStream.values
        (PeriodicCNF.numericRouteDescriptors formula) =
      (values (paddedCarrierNodeCandidateStream
        (PeriodicCNF.numericRouteDescriptors formula))).map fun node =>
          RouteDescriptorCarrierKeyAxisDatum.value
            (PeriodicCNF.numericRouteDescriptors formula)
            (node.map CarrierNode.carrierKey) := by
  rw [carrierKeyAxisValues_numeric_stream
    formula wellFormed degree isLocal forward]
  rw [← map_carrierKey_paddedCarrierNodeCandidateStream]
  rw [values_map_mapValue]
  simp [List.map_map, Function.comp_def]

end LeanTrominoes.PeriodicOrthocrossing

end
