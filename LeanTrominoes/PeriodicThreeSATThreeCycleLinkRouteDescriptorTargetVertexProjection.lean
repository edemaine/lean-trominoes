/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeSplitRouteDescriptorEnumerationData

/-! # Target-index projection of cycle descriptors -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

open PeriodicOrthocrossing

/-- The target-index projection of the cycle descriptors is the index of
each cycle-incidence atom in the rotated occurrence-copy order. -/
theorem cycleLinkRouteDescriptors_targetVertexIndices_eq_atomStream
    {Variable : Type*} [DecidableEq Variable]
    [DecidableEq (ThreeOccurrenceVariable Variable)]
    (source : PeriodicCNF Variable) :
    (cycleLinkRouteDescriptors source).map
        RouteDescriptor.targetVertexIndex =
      ((cycleLinkIncidences source).map
        (fun incidence => incidence.literal.atom)).map fun atom =>
          @List.idxOf (ThreeOccurrenceVariable Variable)
            instBEqOfDecidableEq atom
            (rotatedOccurrenceVariables source) := by
  unfold cycleLinkRouteDescriptors
  rw [List.map_map]
  change ((cycleLinkIncidences source).zipIdx).map
      (fun tagged =>
        @List.idxOf (ThreeOccurrenceVariable Variable)
          instBEqOfDecidableEq tagged.1.literal.atom
          (rotatedOccurrenceVariables source)) = _
  calc
    ((cycleLinkIncidences source).zipIdx).map
        (fun tagged =>
          @List.idxOf (ThreeOccurrenceVariable Variable)
            instBEqOfDecidableEq tagged.1.literal.atom
            (rotatedOccurrenceVariables source)) =
      (((cycleLinkIncidences source).zipIdx).map Prod.fst).map
        (fun incidence =>
          @List.idxOf (ThreeOccurrenceVariable Variable)
            instBEqOfDecidableEq incidence.literal.atom
            (rotatedOccurrenceVariables source)) := by
          rw [List.map_map]
          rfl
    _ = (cycleLinkIncidences source).map
        (fun incidence =>
          @List.idxOf (ThreeOccurrenceVariable Variable)
            instBEqOfDecidableEq incidence.literal.atom
            (rotatedOccurrenceVariables source)) := by
          rw [List.zipIdx_map_fst]
    _ = _ := by
      rw [List.map_map]
      rfl

end PeriodicThreeSATThree
end LeanTrominoes
