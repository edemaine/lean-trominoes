/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorDiagonal
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorSelfIndex
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierKeySlotNumericDiagonalSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierKeySlotOffDiagonalSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairCrossingSemantics

/-! # Numeric terminal carrier-key slot stream semantics -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags
open PaddedSupportedCandidateBlocks

/-- Removing inactive terminal slots from the numeric descriptor square gives
the exact terminal-key prefix of the global neighboring-occurrence stream. -/
theorem terminalCarrierKeyActiveValueStream_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal) :
    (((PeriodicCNF.numericRouteDescriptors formula) ×ˢ
          (PeriodicCNF.numericRouteDescriptors formula)).flatMap fun pair =>
        activeValues
          (terminalCarrierKeyActivations (descriptorPairTokens pair))
          (terminalCarrierKeyTemplateBlocks pair)) =
      occurrenceTerminalCarrierKeys
        (routeDescriptorNeighborOccurrences
          (PeriodicCNF.numericRouteDescriptors formula)) := by
  rw [PeriodicCNF.numericRouteDescriptorSquare_flatMap_eq_diagonal
    formula
    (fun pair =>
      activeValues
        (terminalCarrierKeyActivations (descriptorPairTokens pair))
        (terminalCarrierKeyTemplateBlocks pair))]
  · rw [show
        (PeriodicCNF.numericRouteDescriptors formula).flatMap
            (fun descriptor =>
              activeValues
                (terminalCarrierKeyActivations
                  (descriptorPairTokens (descriptor, descriptor)))
                (terminalCarrierKeyTemplateBlocks
                  (descriptor, descriptor))) =
          (PeriodicCNF.numericRouteDescriptors formula).flatMap
            (fun descriptor => occurrenceTerminalCarrierKeys
              descriptor.selfIndexedNeighborOccurrences) by
      apply List.flatMap_congr
      intro descriptor descriptorMember
      exact terminalCarrierKeyActiveValues_numeric_diagonal
        formula wellFormed degree isLocal forward descriptor
        descriptorMember]
    rw [routeDescriptorNeighborOccurrences_eq_selfIndexedBlocks
      (PeriodicCNF.numericRouteDescriptors formula)
      (PeriodicCNF.numericRouteDescriptors_selfIndexed formula)]
    unfold occurrenceTerminalCarrierKeys
    rw [List.flatMap_assoc]
  · intro first _firstMember second _secondMember edgeIndexNe
    exact terminalCarrierKeyActiveValues_eq_nil_of_edgeIndex_ne
      (first, second) edgeIndexNe

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine
