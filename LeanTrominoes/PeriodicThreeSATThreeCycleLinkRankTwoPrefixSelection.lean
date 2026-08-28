/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkRouteDescriptorRankPairs

/-! # Rank-two cycle descriptors as a prefix-rank selection -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

open PeriodicOrthocrossing
open CycleLinkGroupedPortRanks

/-- The rank-two descriptor scan can be read directly from the aligned atom
and prefix-rank streams. -/
theorem cycleLinkRouteDescriptors_rankTwo_flatMap_eq_prefixRanks
    {Variable Output : Type*} [DecidableEq Variable]
    [DecidableEq (ThreeOccurrenceVariable Variable)]
    (source : PeriodicCNF Variable) (block : Nat → List Output) :
    (cycleLinkRouteDescriptors source).flatMap (fun descriptor =>
        if descriptor.targetPortRank = 2 then
          block descriptor.targetVertexIndex else []) =
      let atoms := (cycleLinkIncidences source).map
        (fun incidence => incidence.literal.atom)
      (atoms.zip (prefixRanks atoms)).flatMap fun pair =>
        if pair.2 = 2 then
          block (@List.idxOf (ThreeOccurrenceVariable Variable)
            instBEqOfDecidableEq pair.1
            (rotatedOccurrenceVariables source))
        else [] := by
  let atoms := (cycleLinkIncidences source).map
    (fun incidence => incidence.literal.atom)
  calc
    (cycleLinkRouteDescriptors source).flatMap (fun descriptor =>
        if descriptor.targetPortRank = 2 then
          block descriptor.targetVertexIndex else []) =
      ((cycleLinkRouteDescriptors source).map (fun descriptor =>
          (descriptor.targetVertexIndex,
            descriptor.targetPortRank))).flatMap (fun pair =>
          if pair.2 = 2 then block pair.1 else []) := by
            rw [List.flatMap_map]
    _ = (((atoms.zip (prefixRanks atoms)).map fun pair =>
          (@List.idxOf (ThreeOccurrenceVariable Variable)
              instBEqOfDecidableEq pair.1
              (rotatedOccurrenceVariables source),
            pair.2)).flatMap fun pair =>
              if pair.2 = 2 then block pair.1 else []) := by
            rw [cycleLinkRouteDescriptors_targetRankPairs]
    _ = (atoms.zip (prefixRanks atoms)).flatMap (fun pair =>
          if pair.2 = 2 then
            block (@List.idxOf (ThreeOccurrenceVariable Variable)
              instBEqOfDecidableEq pair.1
              (rotatedOccurrenceVariables source))
          else []) := by
            rw [List.flatMap_map]

end PeriodicThreeSATThree
end LeanTrominoes
