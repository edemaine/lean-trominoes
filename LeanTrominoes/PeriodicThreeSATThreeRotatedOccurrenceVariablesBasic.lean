/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkIncidenceAtomDedup
import LeanTrominoes.PeriodicThreeSATThreeExactSize

/-! # Basic properties of the rotated occurrence-copy order -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

/-- The rotated occurrence-copy presentation contains no duplicate copy. -/
theorem rotatedOccurrenceVariables_nodup
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (rotatedOccurrenceVariables source).Nodup := by
  rw [← cycleLinkIncidences_atoms_dedup_eq_rotatedOccurrenceVariables]
  exact List.nodup_dedup _

/-- Rotation within occurrence groups preserves the total source-literal
count. -/
@[simp] theorem rotatedOccurrenceVariables_length
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (rotatedOccurrenceVariables source).length =
      PeriodicCNF.presentationLiteralCount source := by
  unfold rotatedOccurrenceVariables rotatedOccurrenceVariablesFor
  rw [List.length_flatMap]
  calc
    ((sourceVariables source).map fun atom =>
        ((occurrenceVariables source atom).tail ++
          (occurrenceVariables source atom).take 1).length).sum =
      ((sourceVariables source).map fun atom =>
        (occurrenceVariables source atom).length).sum := by
          congr 1
          apply List.map_congr_left
          intro atom _atomMember
          cases occurrenceVariables source atom <;> simp
    _ = (taggedLiterals source).length :=
      occurrenceVariables_total_length source
    _ = PeriodicCNF.presentationLiteralCount source :=
      taggedLiterals_length source

end PeriodicThreeSATThree
end LeanTrominoes
