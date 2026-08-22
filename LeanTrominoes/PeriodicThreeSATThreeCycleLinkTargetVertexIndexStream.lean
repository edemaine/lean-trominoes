/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkPortRankSemantics

/-! # Exact target-vertex stream of cycle-link incidences -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree
namespace CycleLinkDescriptorStreams

def interleaveWords {Value : Type*}
    (first second : List Value) : List Value :=
  (first.zip second).flatMap fun pair => [pair.1, pair.2]

theorem interleaveWords_map
    {Input Output : Type*}
    (values : List Input) (first second : Input → Output) :
    interleaveWords (values.map first) (values.map second) =
      values.flatMap fun value => [first value, second value] := by
  induction values with
  | nil => rfl
  | cons value values induction =>
      unfold interleaveWords at induction ⊢
      simp only [List.map_cons, List.zip_cons_cons, List.flatMap_cons]
      rw [induction]

theorem map_linkAtoms
    {Value Output : Type*} (links : List (Value × Value))
    (mapValue : Value → Output) :
    (CycleLinkGroupedPortRanks.linkAtoms links).map mapValue =
      links.flatMap fun link => [mapValue link.1, mapValue link.2] := by
  induction links with
  | nil => rfl
  | cons link links induction =>
      simp only [CycleLinkGroupedPortRanks.linkAtoms, List.map_cons,
        List.flatMap_cons]
      rw [induction]
      rfl

/-- The target-vertex indices of alternating source and target incidences are
the interleaving of the compiled wraparound source indices and consecutive
target indices. -/
theorem cycleLinkIncidences_targetVertexIndices
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (cycleLinkIncidences source).map (fun incidence =>
        @List.idxOf (ThreeOccurrenceVariable Variable)
          instBEqOfDecidableEq incidence.literal.atom
          (rotatedOccurrenceVariables source)) =
      interleaveWords
        (PeriodicCNF.SourceCycleLinkTargetIndices.targetIndices
          ((sourceVariables source).map fun atom =>
            (occurrenceVariables source atom).length))
        (List.range (PeriodicCNF.presentationLiteralCount source)) := by
  calc
    (cycleLinkIncidences source).map (fun incidence =>
        @List.idxOf (ThreeOccurrenceVariable Variable)
          instBEqOfDecidableEq incidence.literal.atom
          (rotatedOccurrenceVariables source)) =
        ((cycleLinkIncidences source).map
          (fun incidence => incidence.literal.atom)).map (fun atom =>
            @List.idxOf (ThreeOccurrenceVariable Variable)
              instBEqOfDecidableEq atom
              (rotatedOccurrenceVariables source)) := by
      rw [List.map_map]
      rfl
    _ = (CycleLinkGroupedPortRanks.linkAtoms
          (allCycleLinks source)).map (fun atom =>
            @List.idxOf (ThreeOccurrenceVariable Variable)
              instBEqOfDecidableEq atom
              (rotatedOccurrenceVariables source)) := by
      rw [CycleLinkGroupedPortRanks.cycleLinkIncidences_atoms]
    _ = (allCycleLinks source).flatMap fun link =>
        [@List.idxOf (ThreeOccurrenceVariable Variable)
            instBEqOfDecidableEq link.1
            (rotatedOccurrenceVariables source),
          @List.idxOf (ThreeOccurrenceVariable Variable)
            instBEqOfDecidableEq link.2
            (rotatedOccurrenceVariables source)] := by
      rw [map_linkAtoms]
    _ = interleaveWords
        ((allCycleLinks source).map fun link =>
          @List.idxOf (ThreeOccurrenceVariable Variable)
            instBEqOfDecidableEq link.1
            (rotatedOccurrenceVariables source))
        ((allCycleLinks source).map fun link =>
          @List.idxOf (ThreeOccurrenceVariable Variable)
            instBEqOfDecidableEq link.2
            (rotatedOccurrenceVariables source)) := by
      exact (interleaveWords_map _ _ _).symm
    _ = _ := by
      rw [CycleLinkGroupedTargetIndices.allCycleLinks_sourceTargetIndices,
        CycleLinkGroupedTargetIndices.allCycleLinks_targetTargetIndices]

end CycleLinkDescriptorStreams
end PeriodicThreeSATThree
end LeanTrominoes
