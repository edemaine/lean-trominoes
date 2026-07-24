import LeanTrominoes.PeriodicOccurrences
import LeanTrominoes.PeriodicThreeSATThreeCorrectness
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sigma

/-!
# Occurrence bound for the periodic 3SAT-3 reduction

Each output variable occurs once in the copied source formula, once as the
tail of an implication, and once as the head of an implication.  This file
proves the resulting literal-occurrence count is at most three.
-/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

/-- Every occurrence-copy variable in presentation order. -/
def allOccurrenceVariables {Variable : Type*}
    (source : PeriodicCNF Variable) :
    List (ThreeOccurrenceVariable Variable) :=
  (taggedLiterals source).map fun tagged =>
    (tagged.1.atom, tagged.2.1, tagged.2.2)

/-- Nested clause/literal positions, written recursively to expose their
strictly increasing outer indices. -/
def occurrenceIndicesFrom {Variable : Type*} :
    Nat → List (PeriodicClause Variable) → List (Nat × Nat)
  | _, [] => []
  | clauseIndex, clause :: rest =>
      clause.zipIdx.map (fun tagged => (clauseIndex, tagged.2)) ++
        occurrenceIndicesFrom (clauseIndex + 1) rest

theorem occurrenceIndicesFrom_eq {Variable : Type*}
    (clauseIndex : Nat) (clauses : List (PeriodicClause Variable)) :
    occurrenceIndicesFrom clauseIndex clauses =
      (clauses.zipIdx clauseIndex).flatMap (fun taggedClause =>
        taggedClause.1.zipIdx.map fun taggedLiteral =>
          (taggedClause.2, taggedLiteral.2)) := by
  induction clauses generalizing clauseIndex with
  | nil => rfl
  | cons clause rest induction =>
      simp [occurrenceIndicesFrom, induction]

theorem occurrenceIndicesFrom_fst_ge {Variable : Type*}
    (clauseIndex : Nat) (clauses : List (PeriodicClause Variable)) :
    ∀ index ∈ occurrenceIndicesFrom clauseIndex clauses,
      clauseIndex ≤ index.1 := by
  induction clauses generalizing clauseIndex with
  | nil => simp [occurrenceIndicesFrom]
  | cons clause rest induction =>
      intro index index_mem
      simp only [occurrenceIndicesFrom, List.mem_append] at index_mem
      rcases index_mem with current_mem | rest_mem
      · simp only [List.mem_map] at current_mem
        rcases current_mem with ⟨tagged, tagged_mem, rfl⟩
        exact le_rfl
      · exact Nat.le_trans (Nat.le_add_right clauseIndex 1)
          (induction (clauseIndex + 1) index rest_mem)

theorem currentOccurrenceIndices_nodup {Variable : Type*}
    (clauseIndex : Nat) (clause : PeriodicClause Variable) :
    (clause.zipIdx.map fun tagged => (clauseIndex, tagged.2)).Nodup := by
  have indicesNodup := List.nodup_zipIdx_map_snd clause
  have mapped := indicesNodup.map
    (fun first second equal => congrArg Prod.snd equal :
      Function.Injective (fun literalIndex : Nat =>
        (clauseIndex, literalIndex)))
  simpa only [List.map_map, Function.comp_def] using mapped

theorem occurrenceIndicesFrom_nodup {Variable : Type*}
    (clauseIndex : Nat) (clauses : List (PeriodicClause Variable)) :
    (occurrenceIndicesFrom clauseIndex clauses).Nodup := by
  induction clauses generalizing clauseIndex with
  | nil => simp [occurrenceIndicesFrom]
  | cons clause rest induction =>
      rw [occurrenceIndicesFrom, List.nodup_append]
      refine ⟨currentOccurrenceIndices_nodup clauseIndex clause,
        induction (clauseIndex + 1), ?_⟩
      intro current current_mem later later_mem equal
      have current_fst : current.1 = clauseIndex := by
        simp only [List.mem_map] at current_mem
        rcases current_mem with ⟨tagged, tagged_mem, rfl⟩
        rfl
      have later_ge : clauseIndex + 1 ≤ later.1 :=
        occurrenceIndicesFrom_fst_ge (clauseIndex + 1) rest
          later later_mem
      rw [← equal, current_fst] at later_ge
      omega

theorem allOccurrenceVariables_indices {Variable : Type*}
    (source : PeriodicCNF Variable) :
    (allOccurrenceVariables source).map
        (fun copy => (copy.2.1, copy.2.2)) =
      occurrenceIndicesFrom 0 source.clauses := by
  rw [occurrenceIndicesFrom_eq]
  simp [allOccurrenceVariables, taggedLiterals, List.map_flatMap,
    Function.comp_def]

/-- Positional occurrence copies are pairwise distinct, even when source
clauses or literals are repeated syntactically. -/
theorem allOccurrenceVariables_nodup {Variable : Type*}
    (source : PeriodicCNF Variable) :
    (allOccurrenceVariables source).Nodup := by
  apply List.Nodup.of_map (fun copy => (copy.2.1, copy.2.2))
  rw [allOccurrenceVariables_indices]
  exact occurrenceIndicesFrom_nodup 0 source.clauses

theorem occurrenceClauses_variableOccurrences {Variable : Type*}
    (source : PeriodicCNF Variable) :
    PeriodicCNF.variableOccurrences
        (PeriodicCNF.mk (occurrenceClauses source)) =
      allOccurrenceVariables source := by
  simp [PeriodicCNF.variableOccurrences, occurrenceClauses,
    occurrenceClause, allOccurrenceVariables, taggedLiterals,
    List.map_flatMap, List.flatMap_map, List.map_map, Function.comp_def,
    occurrenceLiteral]

theorem occurrenceVariables_eq_filter {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (atom : Variable) :
    occurrenceVariables source atom =
      (allOccurrenceVariables source).filter
        (fun copy => decide (copy.1 = atom)) := by
  unfold occurrenceVariables allOccurrenceVariables
  induction taggedLiterals source with
  | nil => rfl
  | cons tagged rest induction =>
      by_cases same : tagged.1.atom = atom
      · simp [same, induction]
      · simp [same, induction]

theorem occurrenceVariables_nodup {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (atom : Variable) :
    (occurrenceVariables source atom).Nodup := by
  rw [occurrenceVariables_eq_filter]
  exact (allOccurrenceVariables_nodup source).filter _

theorem cycleFrom_count {Variable : Type*}
    [DecidableEq Variable]
    (copy first current : ThreeOccurrenceVariable Variable)
    (rest : List (ThreeOccurrenceVariable Variable)) :
    (PeriodicCNF.variableOccurrences
        (PeriodicCNF.mk (cycleFrom first current rest))).count copy =
      (current :: rest).count copy +
        (rest ++ [first]).count copy := by
  induction rest generalizing current with
  | nil =>
      rw [cycleFrom]
      unfold PeriodicCNF.variableOccurrences
      simp only [List.flatMap_cons, List.flatMap_nil, implicationClause,
        List.map_cons, List.map_nil, List.append_nil]
      rw [show [current, first] = [current] ++ [first] by rfl,
        List.count_append]
      simp
  | cons next rest induction =>
      rw [cycleFrom]
      unfold PeriodicCNF.variableOccurrences
      rw [List.flatMap_cons, List.count_append]
      change
        ((implicationClause current next).map
            PeriodicLiteral.atom).count copy +
            (PeriodicCNF.variableOccurrences
              (PeriodicCNF.mk (cycleFrom first next rest))).count copy =
          (current :: next :: rest).count copy +
            ((next :: rest) ++ [first]).count copy
      rw [induction next]
      simp only [implicationClause, List.map_cons, List.map_nil,
        List.count_cons, List.count_append, List.count_nil]
      omega

/-- In a cycle over a duplicate-free list, each copy occurs in exactly its
incoming and outgoing implication literals, hence at most twice. -/
theorem cycleClauses_count_le_two {Variable : Type*}
    [DecidableEq Variable]
    (copies : List (ThreeOccurrenceVariable Variable))
    (copiesNodup : copies.Nodup)
    (copy : ThreeOccurrenceVariable Variable) :
    (PeriodicCNF.variableOccurrences
      (PeriodicCNF.mk (cycleClauses copies))).count copy ≤ 2 := by
  cases copies with
  | nil =>
      simp [cycleClauses, PeriodicCNF.variableOccurrences]
  | cons first rest =>
      rw [show cycleClauses (first :: rest) =
        cycleFrom first first rest by rfl]
      rw [cycleFrom_count]
      have count_le_one :=
        (List.nodup_iff_count_le_one.mp copiesNodup) copy
      have sameCount :
          (rest ++ [first]).count copy =
            (first :: rest).count copy := by
        simp only [List.count_append, List.count_cons,
          List.count_nil]
        omega
      rw [sameCount]
      omega

theorem cycleFrom_occurrences_fst {Variable : Type*}
    [DecidableEq Variable]
    (atom : Variable)
    (first current : ThreeOccurrenceVariable Variable)
    (rest : List (ThreeOccurrenceVariable Variable))
    (firstOriginal : first.1 = atom)
    (currentOriginal : current.1 = atom)
    (restOriginal : ∀ copy ∈ rest, copy.1 = atom) :
    ∀ copy ∈ PeriodicCNF.variableOccurrences
        (PeriodicCNF.mk (cycleFrom first current rest)),
      copy.1 = atom := by
  induction rest generalizing current with
  | nil =>
      intro copy copy_mem
      simp only [cycleFrom, PeriodicCNF.variableOccurrences,
        List.flatMap_cons, List.flatMap_nil, implicationClause,
        List.map_cons, List.map_nil, List.append_nil, List.mem_cons,
        List.not_mem_nil, or_false] at copy_mem
      rcases copy_mem with rfl | rfl
      · exact currentOriginal
      · exact firstOriginal
  | cons next rest induction =>
      intro copy copy_mem
      simp only [cycleFrom, PeriodicCNF.variableOccurrences,
        List.flatMap_cons, implicationClause, List.map_cons, List.map_nil,
        List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at copy_mem
      rcases copy_mem with head_mem | copy_mem
      · rcases head_mem with copy_eq | copy_eq
        · subst copy
          exact currentOriginal
        · subst copy
          exact restOriginal next (by simp)
      · exact induction next (restOriginal next (by simp))
          (fun later later_mem => restOriginal later (by simp [later_mem]))
          copy copy_mem

theorem cycleClauses_occurrences_fst {Variable : Type*}
    [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable) :
    ∀ copy ∈ PeriodicCNF.variableOccurrences
        (PeriodicCNF.mk (cycleClauses (occurrenceVariables source atom))),
      copy.1 = atom := by
  cases copies_eq : occurrenceVariables source atom with
  | nil => simp [cycleClauses, PeriodicCNF.variableOccurrences]
  | cons first rest =>
      have firstOriginal : first.1 = atom :=
        occurrenceVariables_fst source atom
          (copies_eq ▸ List.mem_cons_self)
      have restOriginal : ∀ copy ∈ rest, copy.1 = atom := by
        intro copy copy_mem
        exact occurrenceVariables_fst source atom
          (copies_eq ▸ List.mem_cons_of_mem first copy_mem)
      simpa [copies_eq, cycleClauses] using
        cycleFrom_occurrences_fst atom first first rest
          firstOriginal firstOriginal restOriginal

theorem cycleClauses_count_eq_zero_of_fst_ne {Variable : Type*}
    [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable)
    (copy : ThreeOccurrenceVariable Variable)
    (different : copy.1 ≠ atom) :
    (PeriodicCNF.variableOccurrences
      (PeriodicCNF.mk
        (cycleClauses (occurrenceVariables source atom)))).count copy = 0 := by
  apply List.count_eq_zero_of_not_mem
  intro copy_mem
  exact different
    (cycleClauses_occurrences_fst source atom copy copy_mem)

theorem variableOccurrences_append {Variable : Type*}
    (first second :
      List (PeriodicClause (ThreeOccurrenceVariable Variable))) :
    PeriodicCNF.variableOccurrences
        (PeriodicCNF.mk (first ++ second)) =
      PeriodicCNF.variableOccurrences (PeriodicCNF.mk first) ++
        PeriodicCNF.variableOccurrences (PeriodicCNF.mk second) := by
  simp [PeriodicCNF.variableOccurrences, List.flatMap_append]

/-- Cycle clauses generated for an explicit list of source atoms. -/
def cyclesFor {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atoms : List Variable) :
    List (PeriodicClause (ThreeOccurrenceVariable Variable)) :=
  atoms.flatMap fun atom =>
    cycleClauses (occurrenceVariables source atom)

theorem cyclesFor_count_le {Variable : Type*}
    [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atoms : List Variable)
    (copy : ThreeOccurrenceVariable Variable) :
    (PeriodicCNF.variableOccurrences
      (PeriodicCNF.mk (cyclesFor source atoms))).count copy ≤
        2 * atoms.count copy.1 := by
  induction atoms with
  | nil =>
      simp [cyclesFor, PeriodicCNF.variableOccurrences]
  | cons atom atoms induction =>
      rw [show cyclesFor source (atom :: atoms) =
        cycleClauses (occurrenceVariables source atom) ++
          cyclesFor source atoms by rfl]
      rw [variableOccurrences_append, List.count_append]
      by_cases same : copy.1 = atom
      · have head_le :
            (PeriodicCNF.variableOccurrences
              (PeriodicCNF.mk
                (cycleClauses
                  (occurrenceVariables source atom)))).count copy ≤ 2 :=
          cycleClauses_count_le_two
            (occurrenceVariables source atom)
            (occurrenceVariables_nodup source atom) copy
        have tail_le := induction
        have head_count :
            (atom :: atoms).count copy.1 =
              atoms.count copy.1 + 1 := by
          subst atom
          exact List.count_cons_self
        rw [head_count]
        omega
      · have head_zero :=
          cycleClauses_count_eq_zero_of_fst_ne source atom copy same
        rw [head_zero, zero_add]
        have tail_le := induction
        have head_count :
            (atom :: atoms).count copy.1 =
              atoms.count copy.1 := by
          exact List.count_cons_of_ne
            (fun equal => same equal.symm)
        rw [head_count]
        exact tail_le

theorem allCycleClauses_count_le_two {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (copy : ThreeOccurrenceVariable Variable) :
    (PeriodicCNF.variableOccurrences
      (PeriodicCNF.mk (allCycleClauses source))).count copy ≤ 2 := by
  have sourceVariablesNodup :
      (sourceVariables source).Nodup :=
    List.nodup_dedup _
  have atom_count_le_one :=
    (List.nodup_iff_count_le_one.mp sourceVariablesNodup) copy.1
  have cycles_le :=
    cyclesFor_count_le source (sourceVariables source) copy
  have actual_le :
      (PeriodicCNF.variableOccurrences
        (PeriodicCNF.mk (allCycleClauses source))).count copy ≤
          2 * (sourceVariables source).count copy.1 := by
    simpa [allCycleClauses, cyclesFor] using cycles_le
  omega

theorem occurrenceClauses_count_le_one {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (copy : ThreeOccurrenceVariable Variable) :
    (PeriodicCNF.variableOccurrences
      (PeriodicCNF.mk (occurrenceClauses source))).count copy ≤ 1 := by
  rw [occurrenceClauses_variableOccurrences]
  exact (List.nodup_iff_count_le_one.mp
    (allOccurrenceVariables_nodup source)) copy

/-- Every output protovariable has at most three literal occurrences: one in
the copied source clauses and two in its implication cycle. -/
theorem formula_occurrencesAtMostThree {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable) :
    (formula source).OccurrencesAtMost 3 := by
  intro copy
  have source_le := occurrenceClauses_count_le_one source copy
  have cycles_le := allCycleClauses_count_le_two source copy
  change
    (PeriodicCNF.variableOccurrences
      (PeriodicCNF.mk
        (occurrenceClauses source ++ allCycleClauses source))).count copy ≤ 3
  rw [variableOccurrences_append, List.count_append]
  omega

end PeriodicThreeSATThree
end LeanTrominoes
