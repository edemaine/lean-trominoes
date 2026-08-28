/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListSumFiberPartition
import LeanTrominoes.PeriodicThreeSATThreeRotatedOccurrenceVariablesBasic

/-! # Target indices in deduplicated cycle-atom order -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

/-- Deduplicated cycle atoms are the rotated occurrence list, whose own
indices enumerate the complete consecutive target range. -/
theorem cycleLinkIncidenceAtoms_dedup_targetIndex_flatMap
    {Variable Output : Type*} [DecidableEq Variable]
    [DecidableEq (ThreeOccurrenceVariable Variable)]
    (source : PeriodicCNF Variable) (block : Nat → List Output) :
    (((cycleLinkIncidences source).map
        (fun incidence => incidence.literal.atom)).dedup).flatMap
          (fun atom =>
            block (@List.idxOf (ThreeOccurrenceVariable Variable)
              instBEqOfDecidableEq atom
              (rotatedOccurrenceVariables source))) =
      (List.range (PeriodicCNF.presentationLiteralCount source)).flatMap
        block := by
  rw [cycleLinkIncidences_atoms_dedup_eq_rotatedOccurrenceVariables]
  calc
    (rotatedOccurrenceVariables source).flatMap (fun atom =>
        block (@List.idxOf (ThreeOccurrenceVariable Variable)
          instBEqOfDecidableEq atom
          (rotatedOccurrenceVariables source))) =
      ((rotatedOccurrenceVariables source).map fun atom =>
        @List.idxOf (ThreeOccurrenceVariable Variable)
          instBEqOfDecidableEq atom
          (rotatedOccurrenceVariables source)).flatMap block := by
            rw [List.flatMap_map]
    _ = (List.range (rotatedOccurrenceVariables source).length).flatMap
          block := by
            rw [List.map_idxOf_self_eq_range _
              (rotatedOccurrenceVariables_nodup source)]
    _ = (List.range (PeriodicCNF.presentationLiteralCount source)).flatMap
          block := by rw [rotatedOccurrenceVariables_length]

end PeriodicThreeSATThree
end LeanTrominoes
