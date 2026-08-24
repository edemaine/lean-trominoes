/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkDedupTargetIndexEnumeration
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkRankTwoDedupSelection

/-! # Rank-two selection from the cycle descriptor stream -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

/-- Flat-mapping an arbitrary target-index block over just the rank-two
cycle descriptors visits every occurrence-copy target index exactly once,
in increasing target-index order. -/
theorem cycleLinkRouteDescriptors_rankTwo_flatMap
    {Variable Output : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (block : Nat → List Output) :
    (cycleLinkRouteDescriptors source).flatMap (fun descriptor =>
        if descriptor.targetPortRank = 2 then
          block descriptor.targetVertexIndex else []) =
      (List.range (PeriodicCNF.presentationLiteralCount source)).flatMap
        block := by
  rw [cycleLinkRouteDescriptors_rankTwo_flatMap_eq_dedup,
    cycleLinkIncidenceAtoms_dedup_targetIndex_flatMap]

end PeriodicThreeSATThree
end LeanTrominoes
