import LeanTrominoes.PeriodicEightOccurrenceSplit
import LeanTrominoes.PeriodicThreeSATThreeOccurrences

/-!
# Structural bounds for fixed eight-slot occurrence splitting

The separator-enhanced implication ring contributes two occurrences to every
compass copy.  Its extra separator also has degree two.  If distinct source
occurrences of one atom are assigned distinct compass slots, the copied source
formula contributes at most one more.

This file isolates that geometric hypothesis as `OccurrencePorts.CollisionFree`
and proves the resulting 3SAT-3 occurrence bound.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing

/-- The selected compass copy of every tagged source occurrence, in
presentation order. -/
def selectedCopies {Variable : Type*}
    (source : PeriodicCNF Variable)
    (occurrencePorts : OccurrencePorts) :
    List (ThreeOccurrenceVariable Variable) :=
  (PeriodicThreeSATThree.taggedLiterals source).map fun tagged =>
    copy tagged.1.atom
      (occurrencePorts.port tagged.2.1 tagged.2.2)

/-- No two source occurrences have been assigned the same output copy.

Because `copy` retains the source atom, this condition only constrains pairs
of occurrences belonging to the same atom. -/
def OccurrencePorts.CollisionFree {Variable : Type*}
    (occurrencePorts : OccurrencePorts)
    (source : PeriodicCNF Variable) : Prop :=
  (selectedCopies source occurrencePorts).Nodup

/-- The copied source clauses name exactly the selected compass copies. -/
theorem occurrenceClauses_variableOccurrences
    {Variable : Type*}
    (source : PeriodicCNF Variable)
    (occurrencePorts : OccurrencePorts) :
    PeriodicCNF.variableOccurrences
        (PeriodicCNF.mk
          (occurrenceClauses source occurrencePorts)) =
      selectedCopies source occurrencePorts := by
  simp [PeriodicCNF.variableOccurrences, occurrenceClauses,
    occurrenceClause, selectedCopies,
    PeriodicThreeSATThree.taggedLiterals, occurrenceLiteral,
    List.map_flatMap, List.flatMap_map, List.map_map,
    Function.comp_def]

/-- The numeric compass encoding is injective. -/
theorem portIndex_injective : Function.Injective portIndex := by
  intro first second
  cases first <;> cases second <;> simp [portIndex]

/-- The established clockwise compass list contains every port once. -/
theorem ports_nodup : ports.Nodup := by
  native_decide

/-- Fixed copies of one source atom are distinguished by their ports. -/
theorem copy_injective {Variable : Type*} (atom : Variable) :
    Function.Injective (copy atom) := by
  intro first second equal
  apply portIndex_injective
  exact congrArg (fun occurrence => occurrence.2.1) equal

/-- The eight source copies and the separator copy are all distinct. -/
theorem ringCopy_injective
    {Variable : Type*} (atom : Variable) :
    Function.Injective (ringCopy atom) := by
  intro first second equal
  cases first with
  | separator =>
      cases second with
      | separator => rfl
      | port second =>
          cases second <;>
            simp [ringCopy, copy, portIndex] at equal
  | port first =>
      cases second with
      | separator =>
          cases first <;>
            simp [ringCopy, copy, portIndex] at equal
      | port second =>
          exact congrArg RingVertex.port
            (copy_injective atom equal)

/-- The nine copies in one separator implication ring are pairwise
distinct. -/
theorem copies_nodup {Variable : Type*} (atom : Variable) :
    (copies atom).Nodup := by
  have verticesNodup :
      OccurrenceSplitRing.cycleVertices.Nodup := by
    native_decide
  exact verticesNodup.map (ringCopy_injective atom)

/-- Every literal in one fixed implication ring belongs to the atom whose
copy list generated that ring. -/
theorem cycleClausesFor_occurrences_fst
    {Variable : Type*} [DecidableEq Variable]
    (atom : Variable) :
    ∀ occurrence ∈ PeriodicCNF.variableOccurrences
        (PeriodicCNF.mk (cycleClausesFor atom)),
      occurrence.1 = atom := by
  cases copiesEqual : copies atom with
  | nil =>
      simp [cycleClausesFor, copiesEqual,
        PeriodicThreeSATThree.cycleClauses,
        PeriodicCNF.variableOccurrences]
  | cons first rest =>
      have firstOriginal : first.1 = atom :=
        copy_fst atom
          (copiesEqual ▸ List.mem_cons_self)
      have restOriginal :
          ∀ occurrence ∈ rest, occurrence.1 = atom := by
        intro occurrence occurrenceMember
        exact copy_fst atom
          (copiesEqual ▸
            List.mem_cons_of_mem first occurrenceMember)
      intro occurrence occurrenceMember
      exact
        PeriodicThreeSATThree.cycleFrom_occurrences_fst
          atom first first rest
          firstOriginal firstOriginal restOriginal
          occurrence
          (by
            simpa [cycleClausesFor, copiesEqual,
              PeriodicThreeSATThree.cycleClauses] using
              occurrenceMember)

/-- A copy belonging to another source atom has count zero in this ring. -/
theorem cycleClausesFor_count_eq_zero_of_fst_ne
    {Variable : Type*} [DecidableEq Variable]
    (atom : Variable)
    (occurrence : ThreeOccurrenceVariable Variable)
    (different : occurrence.1 ≠ atom) :
    (PeriodicCNF.variableOccurrences
      (PeriodicCNF.mk (cycleClausesFor atom))).count occurrence = 0 := by
  apply List.count_eq_zero_of_not_mem
  intro occurrenceMember
  exact different
    (cycleClausesFor_occurrences_fst atom
      occurrence occurrenceMember)

/-- Fixed rings generated for an explicit list of source atoms. -/
def cyclesFor {Variable : Type*}
    (atoms : List Variable) :
    List (PeriodicClause (ThreeOccurrenceVariable Variable)) :=
  atoms.flatMap cycleClausesFor

/-- Across an explicit atom list, a copy occurs at most twice for every
appearance of its source atom. -/
theorem cyclesFor_count_le
    {Variable : Type*} [DecidableEq Variable]
    (atoms : List Variable)
    (occurrence : ThreeOccurrenceVariable Variable) :
    (PeriodicCNF.variableOccurrences
      (PeriodicCNF.mk (cyclesFor atoms))).count occurrence ≤
        2 * atoms.count occurrence.1 := by
  induction atoms with
  | nil =>
      simp [cyclesFor, PeriodicCNF.variableOccurrences]
  | cons atom atoms induction =>
      rw [show cyclesFor (atom :: atoms) =
        cycleClausesFor atom ++ cyclesFor atoms by rfl]
      rw [PeriodicThreeSATThree.variableOccurrences_append,
        List.count_append]
      by_cases same : occurrence.1 = atom
      · have headLe :
            (PeriodicCNF.variableOccurrences
              (PeriodicCNF.mk
                (cycleClausesFor atom))).count occurrence ≤ 2 := by
          rw [cycleClausesFor]
          exact
            PeriodicThreeSATThree.cycleClauses_count_le_two
              (copies atom) (copies_nodup atom) occurrence
        have headCount :
            (atom :: atoms).count occurrence.1 =
              atoms.count occurrence.1 + 1 := by
          subst atom
          exact List.count_cons_self
        rw [headCount]
        omega
      · rw [cycleClausesFor_count_eq_zero_of_fst_ne
          atom occurrence same, zero_add]
        have headCount :
            (atom :: atoms).count occurrence.1 =
              atoms.count occurrence.1 :=
          List.count_cons_of_ne
            (fun equal => same equal.symm)
        rw [headCount]
        exact induction

/-- Every fixed compass copy occurs at most twice among all implication
rings. -/
theorem allCycleClauses_count_le_two
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (occurrence : ThreeOccurrenceVariable Variable) :
    (PeriodicCNF.variableOccurrences
      (PeriodicCNF.mk
        (allCycleClauses source))).count occurrence ≤ 2 := by
  have sourceVariablesNodup :
      (PeriodicThreeSATThree.sourceVariables source).Nodup :=
    List.nodup_dedup _
  have atomCountLeOne :=
    (List.nodup_iff_count_le_one.mp
      sourceVariablesNodup) occurrence.1
  have cyclesLe :=
    cyclesFor_count_le
      (PeriodicThreeSATThree.sourceVariables source) occurrence
  have actualLe :
      (PeriodicCNF.variableOccurrences
        (PeriodicCNF.mk
          (allCycleClauses source))).count occurrence ≤
        2 *
          (PeriodicThreeSATThree.sourceVariables source).count
            occurrence.1 := by
    simpa [allCycleClauses, cyclesFor] using cyclesLe
  omega

/-- Collision freedom limits the copied source part to one occurrence of
each fixed compass copy. -/
theorem occurrenceClauses_count_le_one
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (occurrencePorts : OccurrencePorts)
    (collisionFree : occurrencePorts.CollisionFree source)
    (occurrence : ThreeOccurrenceVariable Variable) :
    (PeriodicCNF.variableOccurrences
      (PeriodicCNF.mk
        (occurrenceClauses source occurrencePorts))).count occurrence ≤ 1 := by
  rw [occurrenceClauses_variableOccurrences]
  exact
    (List.nodup_iff_count_le_one.mp collisionFree) occurrence

/-- A collision-free compass assignment gives the required 3SAT-3 bound:
one copied source literal and two implication literals. -/
theorem formula_occurrencesAtMostThree
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (occurrencePorts : OccurrencePorts)
    (collisionFree : occurrencePorts.CollisionFree source) :
    (formula source occurrencePorts).OccurrencesAtMost 3 := by
  intro occurrence
  have sourceLe :=
    occurrenceClauses_count_le_one source occurrencePorts
      collisionFree occurrence
  have cyclesLe :=
    allCycleClauses_count_le_two source occurrence
  change
    (PeriodicCNF.variableOccurrences
      (PeriodicCNF.mk
        (occurrenceClauses source occurrencePorts ++
          allCycleClauses source))).count occurrence ≤ 3
  rw [PeriodicThreeSATThree.variableOccurrences_append,
    List.count_append]
  omega

end PeriodicEightOccurrenceSplit
end LeanTrominoes
