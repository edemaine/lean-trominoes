/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeOccurrences

/-! # Exact occurrence counts inside the splitting cycles -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

/-- Every member of a duplicate-free cycle occurs once incoming and once
outgoing, including the singleton cycle. -/
theorem cycleClauses_count_eq_two_of_mem
    {Variable : Type*} [DecidableEq Variable]
    (copies : List (ThreeOccurrenceVariable Variable))
    (copiesNodup : copies.Nodup)
    (copy : ThreeOccurrenceVariable Variable)
    (copyMember : copy ∈ copies) :
    (PeriodicCNF.variableOccurrences
      (PeriodicCNF.mk (cycleClauses copies))).count copy = 2 := by
  cases copies with
  | nil => simp at copyMember
  | cons first rest =>
      rw [show cycleClauses (first :: rest) =
        cycleFrom first first rest by rfl]
      rw [cycleFrom_count]
      have countOne : (first :: rest).count copy = 1 :=
        List.count_eq_one_of_mem copiesNodup copyMember
      have sameCount :
          (rest ++ [first]).count copy =
            (first :: rest).count copy := by
        simp only [List.count_append, List.count_cons,
          List.count_nil]
        omega
      rw [sameCount, countOne]

theorem cyclesFor_count_eq_zero_of_fst_not_mem
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atoms : List Variable)
    (copy : ThreeOccurrenceVariable Variable)
    (absent : copy.1 ∉ atoms) :
    (PeriodicCNF.variableOccurrences
      (PeriodicCNF.mk (cyclesFor source atoms))).count copy = 0 := by
  induction atoms with
  | nil => simp [cyclesFor, PeriodicCNF.variableOccurrences]
  | cons atom atoms induction =>
      have different : copy.1 ≠ atom := by
        intro equal
        exact absent (by simp [equal])
      have tailAbsent : copy.1 ∉ atoms := by
        simp only [List.mem_cons, not_or] at absent
        exact absent.2
      rw [show cyclesFor source (atom :: atoms) =
        cycleClauses (occurrenceVariables source atom) ++
          cyclesFor source atoms by rfl]
      rw [variableOccurrences_append, List.count_append,
        cycleClauses_count_eq_zero_of_fst_ne
          source atom copy different,
        induction tailAbsent]

theorem cyclesFor_count_eq_two_of_mem
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atoms : List Variable) (atomsNodup : atoms.Nodup)
    (copy : ThreeOccurrenceVariable Variable)
    (atomMember : copy.1 ∈ atoms)
    (copyMember : copy ∈ occurrenceVariables source copy.1) :
    (PeriodicCNF.variableOccurrences
      (PeriodicCNF.mk (cyclesFor source atoms))).count copy = 2 := by
  induction atoms with
  | nil => simp at atomMember
  | cons atom atoms induction =>
      have atomNotMember : atom ∉ atoms :=
        (List.nodup_cons.mp atomsNodup).1
      have atomsNodup' : atoms.Nodup :=
        (List.nodup_cons.mp atomsNodup).2
      rw [show cyclesFor source (atom :: atoms) =
        cycleClauses (occurrenceVariables source atom) ++
          cyclesFor source atoms by rfl]
      rw [variableOccurrences_append, List.count_append]
      by_cases same : copy.1 = atom
      · subst atom
        rw [cycleClauses_count_eq_two_of_mem
          (occurrenceVariables source copy.1)
          (occurrenceVariables_nodup source copy.1)
          copy copyMember]
        have tailAbsent : copy.1 ∉ atoms := atomNotMember
        rw [cyclesFor_count_eq_zero_of_fst_not_mem
          source atoms copy tailAbsent, Nat.add_zero]
      · have headZero :=
          cycleClauses_count_eq_zero_of_fst_ne
            source atom copy same
        rw [headZero, Nat.zero_add]
        apply induction atomsNodup'
        simpa [same] using atomMember

/-- The cycle family contributes exactly two uses of every positional source
occurrence. -/
theorem allCycleClauses_count_eq_two_of_mem_allOccurrenceVariables
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (copy : ThreeOccurrenceVariable Variable)
    (copyMember : copy ∈ allOccurrenceVariables source) :
    (PeriodicCNF.variableOccurrences
      (PeriodicCNF.mk (allCycleClauses source))).count copy = 2 := by
  have atomMember : copy.1 ∈ sourceVariables source := by
    unfold sourceVariables
    rw [List.mem_dedup]
    have mappedMember :
        copy.1 ∈ (allOccurrenceVariables source).map Prod.fst :=
      List.mem_map.mpr ⟨copy, copyMember, rfl⟩
    simpa [allOccurrenceVariables, List.map_map,
      Function.comp_def] using mappedMember
  have copyOwnMember :
      copy ∈ occurrenceVariables source copy.1 := by
    rw [occurrenceVariables_eq_filter]
    exact List.mem_filter.mpr ⟨copyMember, by simp⟩
  simpa [allCycleClauses, cyclesFor] using
    cyclesFor_count_eq_two_of_mem source
      (sourceVariables source) (List.nodup_dedup _)
      copy atomMember copyOwnMember

end PeriodicThreeSATThree
end LeanTrominoes
