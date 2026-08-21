/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeExactVariableEnumeration

/-! # Exact formula variable order after occurrence splitting -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

/-- Exact last-occurrence order contributed by cycles for an explicit source
variable order. -/
def rotatedOccurrenceVariablesFor
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atoms : List Variable) :
    List (ThreeOccurrenceVariable Variable) :=
  atoms.flatMap fun atom =>
    let copies := occurrenceVariables source atom
    copies.tail ++ copies.take 1

/-- Exact variable-vertex order of the complete occurrence-split formula. -/
def rotatedOccurrenceVariables
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    List (ThreeOccurrenceVariable Variable) :=
  rotatedOccurrenceVariablesFor source (sourceVariables source)

theorem cyclesFor_variableOccurrences_fst_mem
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atoms : List Variable) :
    ∀ copy ∈ PeriodicCNF.variableOccurrences
        (PeriodicCNF.mk (cyclesFor source atoms)),
      copy.1 ∈ atoms := by
  intro copy copyMember
  unfold cyclesFor at copyMember
  rw [variableOccurrences_flatMap, List.mem_flatMap] at copyMember
  obtain ⟨atom, atomMember, copyMember⟩ := copyMember
  rw [cycleClauses_occurrences_fst source atom copy copyMember]
  exact atomMember

/-- Distinct source atoms contribute disjoint occurrence-cycle blocks. -/
theorem cycleClauses_variableOccurrences_disjoint_cyclesFor
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable)
    (atoms : List Variable) (atomNotMem : atom ∉ atoms) :
    List.Disjoint
      (PeriodicCNF.variableOccurrences
        (PeriodicCNF.mk
          (cycleClauses (occurrenceVariables source atom))))
      (PeriodicCNF.variableOccurrences
        (PeriodicCNF.mk (cyclesFor source atoms))) := by
  rw [List.disjoint_left]
  intro copy headMember tailMember
  have headAtom :=
    cycleClauses_occurrences_fst source atom copy headMember
  have tailAtom :=
    cyclesFor_variableOccurrences_fst_mem source atoms copy tailMember
  exact atomNotMem (headAtom ▸ tailAtom)

/-- Deduplicating all explicit cycle blocks concatenates their one-step
rotations without cross-block reordering. -/
theorem cyclesFor_variableOccurrences_dedup_eq_rotated
    {Variable : Type*} [DecidableEq Variable]
    [DecidableEq (ThreeOccurrenceVariable Variable)]
    (source : PeriodicCNF Variable) (atoms : List Variable)
    (atomsNodup : atoms.Nodup) :
    (PeriodicCNF.variableOccurrences
      (PeriodicCNF.mk (cyclesFor source atoms))).dedup =
        rotatedOccurrenceVariablesFor source atoms := by
  induction atoms with
  | nil => rfl
  | cons atom atoms induction =>
      have atomNotMem : atom ∉ atoms :=
        (List.nodup_cons.mp atomsNodup).1
      have atomsNodup' : atoms.Nodup :=
        (List.nodup_cons.mp atomsNodup).2
      rw [show cyclesFor source (atom :: atoms) =
          cycleClauses (occurrenceVariables source atom) ++
            cyclesFor source atoms by rfl,
        variableOccurrences_append,
        List.Disjoint.dedup_append
          (cycleClauses_variableOccurrences_disjoint_cyclesFor
            source atom atoms atomNotMem),
        cycleClauses_variableOccurrences_dedup_of_nodup
          (occurrenceVariables source atom)
          (occurrenceVariables_nodup source atom),
        induction atomsNodup']
      rfl

/-- The cycle suffix alone has the exact grouped-and-rotated occurrence
order. -/
theorem allCycleClauses_variableOccurrences_dedup_eq_rotated
    {Variable : Type*} [DecidableEq Variable]
    [DecidableEq (ThreeOccurrenceVariable Variable)]
    (source : PeriodicCNF Variable) :
    (PeriodicCNF.variableOccurrences
      (PeriodicCNF.mk (allCycleClauses source))).dedup =
        rotatedOccurrenceVariables source := by
  simpa [allCycleClauses, cyclesFor, rotatedOccurrenceVariables] using
    cyclesFor_variableOccurrences_dedup_eq_rotated source
      (sourceVariables source) (List.nodup_dedup _)

/-- Because every positional copy occurs in its cycle, the cycle suffix
determines the exact last-occurrence order of the complete formula. -/
theorem formula_variableOccurrences_dedup_eq_rotatedOccurrenceVariables
    {Variable : Type*} [DecidableEq Variable]
    [DecidableEq (ThreeOccurrenceVariable Variable)]
    (source : PeriodicCNF Variable) :
    (PeriodicCNF.variableOccurrences (formula source)).dedup =
      rotatedOccurrenceVariables source := by
  let cycleOccurrences :=
    PeriodicCNF.variableOccurrences
      (PeriodicCNF.mk (allCycleClauses source))
  have originalsSubset :
      allOccurrenceVariables source ⊆ cycleOccurrences := by
    intro copy copyMember
    rw [← List.count_pos_iff]
    rw [allCycleClauses_count_eq_two_of_mem_allOccurrenceVariables
      source copy copyMember]
    omega
  rw [show PeriodicCNF.variableOccurrences (formula source) =
      allOccurrenceVariables source ++ cycleOccurrences by
        unfold formula cycleOccurrences
        rw [variableOccurrences_append,
          occurrenceClauses_variableOccurrences],
    List.Subset.dedup_append_right originalsSubset]
  exact allCycleClauses_variableOccurrences_dedup_eq_rotated source

end PeriodicThreeSATThree
end LeanTrominoes
