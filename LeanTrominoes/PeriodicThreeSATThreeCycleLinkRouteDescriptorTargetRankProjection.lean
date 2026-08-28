/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkPortRankSemantics
import LeanTrominoes.PeriodicThreeSATThreeSplitRouteDescriptorEnumerationData

/-! # Target-rank projection of cycle descriptors -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

open PeriodicOrthocrossing
open CycleLinkGroupedPortRanks

/-- The target-rank projection of the cycle descriptors is the stable
one-based prefix-rank word of the cycle-incidence atoms. -/
theorem cycleLinkRouteDescriptors_targetPortRanks_eq_prefixRanks
    {Variable : Type*} [DecidableEq Variable]
    [DecidableEq (ThreeOccurrenceVariable Variable)]
    (source : PeriodicCNF Variable) :
    (cycleLinkRouteDescriptors source).map
        RouteDescriptor.targetPortRank =
      prefixRanks ((cycleLinkIncidences source).map
        (fun incidence => incidence.literal.atom)) := by
  unfold cycleLinkRouteDescriptors
  rw [List.map_map]
  simp only [Function.comp_def, cycleLinkRouteDescriptor]
  change cycleLinkIncidenceTargetPortRanks source = _
  exact cycleLinkIncidenceTargetPortRanks_eq_prefixRanks source

end PeriodicThreeSATThree
end LeanTrominoes
