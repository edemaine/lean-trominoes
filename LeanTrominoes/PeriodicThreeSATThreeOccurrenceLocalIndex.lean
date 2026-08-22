/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingPortRankPrefix
import LeanTrominoes.PeriodicThreeSATThreeOccurrences

/-! # Local indices of occurrence copies within atom blocks -/

namespace LeanTrominoes

namespace List

theorem count_map_eq_filter_length_decide
    {α β : Type*} [DecidableEq β]
    (values : List α) (field : α → β) (target : β) :
    (values.map field).count target =
      (values.filter fun value => decide (field value = target)).length := by
  induction values with
  | nil => rfl
  | cons value values induction =>
      by_cases same : field value = target <;> simp [same, induction]

end List

namespace PeriodicThreeSATThree

/-- A positional occurrence copy's index within its atom-filtered block is
the number of equal atoms strictly before its source position. -/
theorem occurrenceVariables_idxOf_eq_priorAtomCount
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (tagged : ThreeOccurrenceVariable Variable × Nat)
    (taggedMember : tagged ∈ (allOccurrenceVariables source).zipIdx) :
    @List.idxOf (ThreeOccurrenceVariable Variable)
        instBEqOfDecidableEq tagged.1
        (occurrenceVariables source tagged.1.1) =
      (((allOccurrenceVariables source).take tagged.2).map Prod.fst).count
        tagged.1.1 := by
  let stream := allOccurrenceVariables source
  letI : BEq (ThreeOccurrenceVariable Variable) :=
    instBEqOfDecidableEq
  have copyMember : tagged.1 ∈ stream :=
    List.fst_mem_of_mem_zipIdx taggedMember
  have indexEq : @List.idxOf (ThreeOccurrenceVariable Variable)
      instBEqOfDecidableEq tagged.1 stream = tagged.2 := by
    have indexLt : tagged.2 < stream.length :=
      List.snd_lt_of_mem_zipIdx taggedMember
    have valueEq : stream[tagged.2] = tagged.1 :=
      (List.getElem?_eq_some_iff.mp
        ((List.mem_zipIdx_iff_getElem?).mp taggedMember)).2
    rw [← valueEq]
    exact (allOccurrenceVariables_nodup source).idxOf_getElem
      tagged.2 indexLt
  have selected : decide (tagged.1.1 = tagged.1.1) = true := by simp
  have filteredIndex :=
    List.idxOf_filter_eq_filter_take_idxOf_length
      (fun copy : ThreeOccurrenceVariable Variable =>
        decide (copy.1 = tagged.1.1))
      stream tagged.1 copyMember selected
  calc
    @List.idxOf (ThreeOccurrenceVariable Variable)
        instBEqOfDecidableEq tagged.1
        (occurrenceVariables source tagged.1.1) =
        @List.idxOf (ThreeOccurrenceVariable Variable)
          instBEqOfDecidableEq tagged.1
          (stream.filter fun copy =>
            decide (copy.1 = tagged.1.1)) := by
      rw [occurrenceVariables_eq_filter]
    _ = ((stream.take (@List.idxOf (ThreeOccurrenceVariable Variable)
          instBEqOfDecidableEq tagged.1 stream)).filter fun copy =>
          decide (copy.1 = tagged.1.1)).length := filteredIndex
    _ = (((stream.take (@List.idxOf (ThreeOccurrenceVariable Variable)
          instBEqOfDecidableEq tagged.1 stream)).map Prod.fst).count
          tagged.1.1) := by
      rw [List.count_map_eq_filter_length_decide]
    _ = (((allOccurrenceVariables source).take tagged.2).map
          Prod.fst).count tagged.1.1 := by
      rw [indexEq]

end PeriodicThreeSATThree
end LeanTrominoes
