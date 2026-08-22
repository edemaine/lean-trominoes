/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkRouteEmitterDescriptorProjections
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkRouteDescriptorSkeleton
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkPortRankSemantics

/-! # Varying projections of actual cycle-link descriptors -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree
namespace CycleLinkDescriptorStreams

theorem cycleLinkRouteDescriptors_targetVertexIndices
    (source : PeriodicCNF.SourceSplitRouteDescriptorTokens.Source) :
    (cycleLinkRouteDescriptors source.formula).map
        (·.targetVertexIndex) =
      targetIndexWordsAux 0
        (PeriodicCNF.SourceCycleLinkRouteEmitter.sourceInput
          source).groupSizes := by
  unfold cycleLinkRouteDescriptors
  rw [List.map_map]
  change ((cycleLinkIncidences source.formula).zipIdx).map
      (fun tagged =>
        @List.idxOf (ThreeOccurrenceVariable Nat)
          instBEqOfDecidableEq tagged.1.literal.atom
          (rotatedOccurrenceVariables source.formula)) = _
  calc
    ((cycleLinkIncidences source.formula).zipIdx).map
        (fun tagged =>
          @List.idxOf (ThreeOccurrenceVariable Nat)
            instBEqOfDecidableEq tagged.1.literal.atom
            (rotatedOccurrenceVariables source.formula)) =
        (((cycleLinkIncidences source.formula).zipIdx).map Prod.fst).map
          (fun incidence =>
            @List.idxOf (ThreeOccurrenceVariable Nat)
              instBEqOfDecidableEq incidence.literal.atom
              (rotatedOccurrenceVariables source.formula)) := by
      rw [List.map_map]
      rfl
    _ = (cycleLinkIncidences source.formula).map
          (fun incidence =>
            @List.idxOf (ThreeOccurrenceVariable Nat)
              instBEqOfDecidableEq incidence.literal.atom
              (rotatedOccurrenceVariables source.formula)) := by
      rw [List.zipIdx_map_fst]
    _ = targetIndexWordsAux 0
        ((sourceVariables source.formula).map fun atom =>
          (occurrenceVariables source.formula atom).length) :=
      cycleLinkIncidences_targetVertexIndices_eq_positionWords
        source.formula

theorem cycleLinkRouteDescriptors_targetPortRanks
    (source : PeriodicCNF.SourceSplitRouteDescriptorTokens.Source) :
    (cycleLinkRouteDescriptors source.formula).map
        (·.targetPortRank) =
      (PeriodicCNF.SourceCycleLinkRouteEmitter.sourceInput
        source).groupSizes.flatMap
          CycleLinkGroupedPortRanks.positionalRankWord := by
  unfold cycleLinkRouteDescriptors
  rw [List.map_map]
  change CycleLinkGroupedPortRanks.cycleLinkIncidenceTargetPortRanks
      source.formula = _
  calc
    CycleLinkGroupedPortRanks.cycleLinkIncidenceTargetPortRanks
        source.formula =
      (sourceVariables source.formula).flatMap fun atom =>
        CycleLinkGroupedPortRanks.positionalRankWord
          (occurrenceVariables source.formula atom).length :=
      CycleLinkGroupedPortRanks.cycleLinkIncidenceTargetPortRanks_eq_positional
        source.formula
    _ = ((sourceVariables source.formula).map fun atom =>
          (occurrenceVariables source.formula atom).length).flatMap
        CycleLinkGroupedPortRanks.positionalRankWord := by
      rw [List.flatMap_map]

theorem cycleLinkRouteDescriptors_length_eq_emitter
    (source : PeriodicCNF.SourceSplitRouteDescriptorTokens.Source) :
    (cycleLinkRouteDescriptors source.formula).length =
      (PeriodicCNF.SourceCycleLinkRouteEmitter.descriptors
        (PeriodicCNF.SourceCycleLinkRouteEmitter.sourceInput source)).length := by
  rw [cycleLinkRouteDescriptors_length,
    PeriodicCNF.SourceCycleLinkRouteEmitter.descriptors_length,
    PeriodicCNF.SourceCycleLinkRouteEmitter.sourceInput_literalCount]

end CycleLinkDescriptorStreams
end PeriodicThreeSATThree
end LeanTrominoes
