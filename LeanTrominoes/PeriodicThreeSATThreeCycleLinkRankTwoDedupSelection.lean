/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkAtomRankTwoDedup
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkRankTwoPrefixSelection

/-! # Rank-two cycle descriptors in deduplicated atom order -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

/-- Selecting rank-two cycle descriptors is the same as retaining the last
cycle incidence of each atom. -/
theorem cycleLinkRouteDescriptors_rankTwo_flatMap_eq_dedup
    {Variable Output : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (block : Nat → List Output) :
    (cycleLinkRouteDescriptors source).flatMap (fun descriptor =>
        if descriptor.targetPortRank = 2 then
          block descriptor.targetVertexIndex else []) =
      (((cycleLinkIncidences source).map
        (fun incidence => incidence.literal.atom)).dedup).flatMap
          (fun atom =>
            block (@List.idxOf (ThreeOccurrenceVariable Variable)
              instBEqOfDecidableEq atom
              (rotatedOccurrenceVariables source))) := by
  rw [cycleLinkRouteDescriptors_rankTwo_flatMap_eq_prefixRanks]
  exact cycleLinkIncidenceAtoms_rankTwo_flatMap_eq_dedup source
    (fun atom => block (@List.idxOf (ThreeOccurrenceVariable Variable)
      instBEqOfDecidableEq atom (rotatedOccurrenceVariables source)))

end PeriodicThreeSATThree
end LeanTrominoes
