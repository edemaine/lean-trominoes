/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorNodup
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorSegmentGeometry
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorSelfIndex
import LeanTrominoes.PeriodicOrthocrossingTerminalCarrierKeyAxisOffDiagonalSemantics

/-! # Axis semantics of numeric terminal carrier-key pairs -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorCarrierKeyAxisDatum

/-- Every pair in a numeric route-descriptor square has a key-derived padded
terminal axis family. -/
theorem terminalCarrierKeyActiveDatumBlocks_numeric_pair
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (pair : RouteDescriptor × RouteDescriptor)
    (pairMember : pair ∈
      PeriodicCNF.numericRouteDescriptors formula ×ˢ
        PeriodicCNF.numericRouteDescriptors formula) :
    FixedAxisUnaryFields.ActiveDatumBlocks
      (value (PeriodicCNF.numericRouteDescriptors formula))
      (terminalCarrierKeyActivations
        (RouteDescriptorPairFieldTags.descriptorPairTokens pair))
      terminalCarrierKeyRecipeAxisBlocks
      (terminalCarrierKeyTemplateBlocks pair) := by
  have pairMembers := List.mem_product.mp pairMember
  by_cases edgeIndexNe : pair.1.edgeIndex ≠ pair.2.edgeIndex
  · exact terminalCarrierKeyActiveDatumBlocks_of_edgeIndex_ne
      (PeriodicCNF.numericRouteDescriptors formula) pair edgeIndexNe
  · have descriptorsEq : pair.2 = pair.1 :=
      PeriodicCNF.numericRouteDescriptors_eq_of_edgeIndex_eq
        formula pairMembers.2 pairMembers.1
          (not_not.mp edgeIndexNe).symm
    rcases pair with ⟨first, second⟩
    simp only at descriptorsEq
    subst second
    apply terminalCarrierKeyActiveDatumBlocks_diagonal
      (PeriodicCNF.numericRouteDescriptors formula)
      (PeriodicCNF.numericRouteDescriptors_selfIndexed formula)
      first pairMembers.1
    intro segment segmentMember
    exact PeriodicCNF.numericRouteDescriptor_segment_axisAligned
      formula wellFormed degree isLocal pairMembers.1 segmentMember

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
