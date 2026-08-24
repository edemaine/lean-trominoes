/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyAxisNumericNodeStreamSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeCodeSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumLookupData
import LeanTrominoes.PeriodicOrthocrossingNumericRetainedCarrierNodeKeyAxisSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierNodeCandidateStreamSemantics

/-! # Numeric carrier-key axes as carrier rank horizontal fields -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing

open PaddedSupportedLastRepresentativeEqualityRows

/-- On numeric CNF routes, every padded carrier-key axis value is the
horizontal field reconstructed from the aligned carrier-node identity. -/
theorem carrierKeyAxisValues_numeric_horizontalField
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    CarrierKeyAxisStream.values
        (PeriodicCNF.numericRouteDescriptors formula) =
      (values (paddedCarrierNodeCandidateStream
        (PeriodicCNF.numericRouteDescriptors formula))).map fun node =>
          CarrierRankDatumLookup.fieldValueAtPeriod
            (routeDescriptorStreamGridSize
              (PeriodicCNF.numericRouteDescriptors formula))
            (fun datum => if datum.horizontal then 1 else 0)
            (node.map CarrierNode.code) := by
  rw [carrierKeyAxisValues_numeric_nodeStream
    formula wellFormed degree isLocal forward]
  apply List.map_congr_left
  intro nodeOption nodeOptionMember
  cases nodeOption with
  | none => rfl
  | some node =>
      have nodeMemberPadded :
          node ∈ (paddedCarrierNodeCandidateStream
            (PeriodicCNF.numericRouteDescriptors formula)).filterMap
              Candidate.value := by
        unfold values at nodeOptionMember
        rcases List.mem_map.mp nodeOptionMember with
          ⟨candidate, candidateMember, candidateValue⟩
        exact List.mem_filterMap.mpr
          ⟨candidate, candidateMember, candidateValue⟩
      have nodeMember : node ∈ routeDescriptorRetainedCarrierNodesAtPeriod
          (routeDescriptorStreamGridSize
            (PeriodicCNF.numericRouteDescriptors formula))
          (PeriodicCNF.numericRouteDescriptors formula) := by
        rw [← paddedCarrierNodeCandidateStream_numericRouteDescriptors
          formula wellFormed degree isLocal forward nonempty]
        exact nodeMemberPadded
      simpa [CarrierRankDatumLookup.fieldValueAtPeriod,
        carrierNodeRankDatumAtPeriod, FixedAxisUnaryFields.value] using
        numericRetainedCarrierNode_carrierKey_axisValue
          formula nonempty nodeMember

end LeanTrominoes.PeriodicOrthocrossing

end
