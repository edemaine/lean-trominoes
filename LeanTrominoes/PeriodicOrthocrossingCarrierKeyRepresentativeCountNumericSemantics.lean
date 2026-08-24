/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRepresentativeCountRouteSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierKeyCandidateStreamSemantics

/-! # Retained carrier-key counts of numeric CNF routes -/

namespace LeanTrominoes.PeriodicOrthocrossing

open PaddedSupportedLastRepresentativeEqualityRows
open RouteDescriptorPairAffine

/-- On a nonempty forward-local numeric CNF route stream, the compiled unary
counts have the exact retained carrier-key order and multiplicities. -/
theorem paddedCarrierKeyRepresentativeCounts_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    paddedCarrierKeyRepresentativeCounts
        (PeriodicCNF.numericRouteDescriptors formula) =
      (routeDescriptorRetainedCarrierKeysAtPeriod
        (routeDescriptorStreamGridSize
          (PeriodicCNF.numericRouteDescriptors formula))
        (PeriodicCNF.numericRouteDescriptors formula)).map fun key =>
          DelimitedBinaryWordTrueCounts.countTrue
            (LastRepresentativeEqualityRows.equalityRow
              (values (paddedCarrierKeyCandidateStream
                (PeriodicCNF.numericRouteDescriptors formula)))
              (some key)) := by
  apply paddedCarrierKeyRepresentativeCounts_eq_of_routeInvariants
  · exact PeriodicCNF.numericRouteDescriptors_selfIndexed formula
  · exact PeriodicCNF.numericRouteDescriptors_all_hasLocalShape
      formula forward
  · exact paddedTerminalCarrierKeyCandidateStream_numericRouteDescriptors
      formula wellFormed degree isLocal forward
  · exact paddedCarrierKeyCandidateStream_numericRouteDescriptors
      formula wellFormed degree isLocal forward nonempty

end LeanTrominoes.PeriodicOrthocrossing
