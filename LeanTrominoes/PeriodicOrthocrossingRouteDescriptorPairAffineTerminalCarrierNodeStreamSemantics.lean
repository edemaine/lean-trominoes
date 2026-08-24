/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorDiagonal
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorSelfIndex
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierNodeCandidateStreamSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierNodeNumericDiagonalSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierNodeOffDiagonalSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairCrossingSemantics

/-! # Numeric terminal carrier-node stream semantics -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

open PaddedSupportedCandidateBlocks
open PaddedSupportedLastRepresentativeEqualityRows
open RouteDescriptorPairFieldTags

/-- Removing inactive terminal slots from the numeric descriptor square gives
the exact terminal-node prefix of the global neighboring-occurrence stream. -/
theorem paddedTerminalCarrierNodeCandidateStream_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal) :
    (paddedTerminalCarrierNodeCandidateStream
        (PeriodicCNF.numericRouteDescriptors formula)).filterMap
          Candidate.value =
      (routeDescriptorNeighborOccurrences
        (PeriodicCNF.numericRouteDescriptors formula)).flatMap
          occurrenceCarrierTerminalNodes := by
  rw [filterMap_paddedTerminalCarrierNodeCandidateStream]
  rw [PeriodicCNF.numericRouteDescriptorSquare_flatMap_eq_diagonal
    formula
    (fun pair =>
      activeValues
        (terminalCarrierKeyActivations (descriptorPairTokens pair))
        (terminalCarrierNodeTemplateBlocks pair))]
  · rw [show
        (PeriodicCNF.numericRouteDescriptors formula).flatMap
            (fun descriptor =>
              activeValues
                (terminalCarrierKeyActivations
                  (descriptorPairTokens (descriptor, descriptor)))
                (terminalCarrierNodeTemplateBlocks
                  (descriptor, descriptor))) =
          (PeriodicCNF.numericRouteDescriptors formula).flatMap
            (fun descriptor =>
              descriptor.selfIndexedNeighborOccurrences.flatMap
                occurrenceCarrierTerminalNodes) by
      apply List.flatMap_congr
      intro descriptor descriptorMember
      exact terminalCarrierNodeActiveValues_numeric_diagonal
        formula wellFormed degree isLocal forward descriptor
        descriptorMember]
    rw [routeDescriptorNeighborOccurrences_eq_selfIndexedBlocks
      (PeriodicCNF.numericRouteDescriptors formula)
      (PeriodicCNF.numericRouteDescriptors_selfIndexed formula)]
    rw [List.flatMap_assoc]
  · intro first _firstMember second _secondMember edgeIndexNe
    exact terminalCarrierNodeActiveValues_eq_nil_of_edgeIndex_ne
      (first, second) edgeIndexNe

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine
