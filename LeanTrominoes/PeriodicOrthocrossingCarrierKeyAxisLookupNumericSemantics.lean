/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyAxisLookupRetainedOrderSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyAxisNumericStreamKeySemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierKeyCandidateStreamSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierKeyRepresentativeRowSemantics

/-! # Retained carrier-key axes of numeric CNF routes -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyAxisLookup

open RouteDescriptorPairAffine

/-- The compiled lookup returns the descriptor-derived axis bit in exact
retained carrier-key order for a numeric CNF route stream. -/
theorem values_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    values (PeriodicCNF.numericRouteDescriptors formula) =
      (routeDescriptorRetainedCarrierKeysAtPeriod
        (routeDescriptorStreamGridSize
          (PeriodicCNF.numericRouteDescriptors formula))
        (PeriodicCNF.numericRouteDescriptors formula)).map fun key =>
          RouteDescriptorCarrierKeyAxisDatum.value
            (PeriodicCNF.numericRouteDescriptors formula) (some key) := by
  let descriptors := PeriodicCNF.numericRouteDescriptors formula
  have selfIndexed :=
    PeriodicCNF.numericRouteDescriptors_selfIndexed formula
  have localShapes :=
    PeriodicCNF.numericRouteDescriptors_all_hasLocalShape formula forward
  have terminalValues :=
    paddedTerminalCarrierKeyCandidateStream_numericRouteDescriptors
      formula wellFormed degree isLocal forward
  exact values_eq_retainedKeys_map
    (routeDescriptorStreamGridSize descriptors) descriptors
    (paddedCarrierKeyRepresentativeRows_eq_selectedRows
      descriptors selfIndexed localShapes terminalValues)
    (paddedCarrierKeyCandidateStream_correctSupport
      descriptors selfIndexed localShapes terminalValues)
    (paddedCarrierKeyCandidateStream_numericRouteDescriptors
      formula wellFormed degree isLocal forward nonempty)
    (RouteDescriptorCarrierKeyAxisDatum.value descriptors)
    (carrierKeyAxisValues_numeric_stream
      formula wellFormed degree isLocal forward)

end CarrierKeyAxisLookup
end LeanTrominoes.PeriodicOrthocrossing
