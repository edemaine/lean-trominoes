/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingTerminalCarrierKeyAxisBlockSemantics
import LeanTrominoes.PeriodicOrthocrossingTerminalCarrierKeyAxisNumericPairSemantics

/-! # Key-derived values of numeric terminal carrier-key pairs -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open PaddedSupportedLastRepresentativeEqualityRows
open RouteDescriptorCarrierKeyAxisDatum

/-- On every numeric descriptor pair, the compiled padded terminal axes are
the descriptor key-axis datum mapped over the padded candidate values. -/
theorem terminalCarrierKeyAxisValues_numeric_pair
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (pair : RouteDescriptor × RouteDescriptor)
    (pairMember : pair ∈
      PeriodicCNF.numericRouteDescriptors formula ×ˢ
        PeriodicCNF.numericRouteDescriptors formula) :
    terminalCarrierKeyAxisValues
        (RouteDescriptorPairFieldTags.descriptorPairTokens pair) =
      (paddedTerminalCarrierKeyCandidates pair).map
        (value (PeriodicCNF.numericRouteDescriptors formula) ∘
          Candidate.value) := by
  unfold terminalCarrierKeyAxisValues terminalCarrierKeyRecipeAxes
    paddedTerminalCarrierKeyCandidates
  rw [terminalCarrierKeyExpandedActives_eq_axisBlockActives]
  exact FixedAxisUnaryFields.values_blockActives_eq_map_candidates_of_active
    (value (PeriodicCNF.numericRouteDescriptors formula))
    (terminalCarrierKeyActivations
      (RouteDescriptorPairFieldTags.descriptorPairTokens pair))
    terminalCarrierKeyRecipeAxisBlocks
    (terminalCarrierKeyTemplateBlocks pair)
    (terminalCarrierKeyActiveDatumBlocks_numeric_pair
      formula wellFormed degree isLocal pair pairMember)

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
