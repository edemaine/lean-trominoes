/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkRouteDescriptorTargetRankProjection
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkRouteDescriptorTargetVertexProjection

/-! # Target-index and target-rank pairs of cycle descriptors -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

open PeriodicOrthocrossing
open CycleLinkGroupedPortRanks

private theorem map_pair_eq_zip_maps
    {Value First Second : Type*} (values : List Value)
    (first : Value → First) (second : Value → Second) :
    values.map (fun value => (first value, second value)) =
      (values.map first).zip (values.map second) := by
  induction values with
  | nil => rfl
  | cons value values induction =>
      simp only [List.map_cons, List.zip_cons_cons]
      rw [induction]

/-- Pairing the two varying target fields loses no alignment information:
each descriptor carries its incidence atom's rotated index and prefix rank. -/
theorem cycleLinkRouteDescriptors_targetRankPairs
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (cycleLinkRouteDescriptors source).map (fun descriptor =>
        (descriptor.targetVertexIndex, descriptor.targetPortRank)) =
      (((cycleLinkIncidences source).map
          (fun incidence => incidence.literal.atom)).zip
        (prefixRanks ((cycleLinkIncidences source).map
          (fun incidence => incidence.literal.atom)))).map fun pair =>
            (@List.idxOf (ThreeOccurrenceVariable Variable)
                instBEqOfDecidableEq pair.1
                (rotatedOccurrenceVariables source),
              pair.2) := by
  rw [map_pair_eq_zip_maps,
    cycleLinkRouteDescriptors_targetVertexIndices_eq_atomStream,
    cycleLinkRouteDescriptors_targetPortRanks_eq_prefixRanks,
    List.zip_map_left]
  apply List.map_congr_left
  intro pair _pairMember
  cases pair
  rfl

end PeriodicThreeSATThree
end LeanTrominoes
