/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFixedEightData
import LeanTrominoes.PeriodicEightOccurrenceSplitOccurrences
import LeanTrominoes.PeriodicThreeSATThreeExactVariableCount

/-! # Exact distinct-variable count after fixed-eight splitting -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

/-- Every output copy, grouped by the deduplicated source-variable order. -/
def allCopies {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    List (ThreeOccurrenceVariable Variable) :=
  (PeriodicThreeSATThree.sourceVariables source).flatMap copies

/-- Every compass copy occurs in the nine-copy list. -/
theorem copy_mem_copies {Variable : Type*}
    (atom : Variable) (port : OccurrenceSplitRing.Port) :
    copy atom port ∈ copies atom := by
  unfold copies
  apply List.mem_map.mpr
  refine ⟨.port port, ?_, rfl⟩
  cases port <;> simp [OccurrenceSplitRing.cycleVertices]

@[simp] theorem copies_length {Variable : Type*} (atom : Variable) :
    (copies atom).length =
      PeriodicCNF.FormulaShapeFixedEight.copiesPerVariable := by
  rfl

/-- The source-variable list is exactly the deduplicated presentation
occurrence list. -/
theorem taggedLiterals_atoms
    {Variable : Type*} (source : PeriodicCNF Variable) :
    (PeriodicThreeSATThree.taggedLiterals source).map
        (fun tagged => tagged.1.atom) =
      source.variableOccurrences := by
  unfold PeriodicThreeSATThree.taggedLiterals
    PeriodicCNF.variableOccurrences
  rw [List.map_flatMap]
  calc
    source.clauses.zipIdx.flatMap
          (fun taggedClause =>
            (taggedClause.1.zipIdx.map fun taggedLiteral =>
              (taggedLiteral.1, taggedClause.2,
                taggedLiteral.2)).map
              fun tagged => tagged.1.atom) =
        source.clauses.zipIdx.flatMap
          (fun taggedClause =>
            taggedClause.1.map PeriodicLiteral.atom) := by
      apply List.flatMap_congr
      intro taggedClause _
      have functionEq :
          ((fun tagged : PeriodicLiteral Variable × Nat × Nat =>
              tagged.1.atom) ∘
            fun taggedLiteral : PeriodicLiteral Variable × Nat =>
              (taggedLiteral.1, taggedClause.2,
                taggedLiteral.2)) =
            PeriodicLiteral.atom ∘ Prod.fst := by
        funext taggedLiteral
        rfl
      have literals := congrArg (List.map PeriodicLiteral.atom)
        (List.zipIdx_map_fst 0 taggedClause.1)
      rw [List.map_map, functionEq]
      simpa only [List.map_map] using literals
    _ = source.clauses.flatMap
          (fun clause => clause.map PeriodicLiteral.atom) := by
      have clauses := congrArg
        (List.flatMap fun clause =>
          clause.map PeriodicLiteral.atom)
        (List.zipIdx_map_fst 0 source.clauses)
      simpa only [List.flatMap_map, Function.comp_apply] using clauses

theorem sourceVariables_eq_variableOccurrences_dedup
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    PeriodicThreeSATThree.sourceVariables source =
      source.variableOccurrences.dedup := by
  unfold PeriodicThreeSATThree.sourceVariables
  rw [taggedLiterals_atoms]

/-- Copy blocks belonging to distinct source atoms are disjoint, and every
individual nine-copy block is duplicate-free. -/
theorem allCopies_nodup {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (allCopies source).Nodup := by
  unfold allCopies
  rw [List.nodup_flatMap]
  constructor
  · intro atom _
    exact copies_nodup atom
  · have atomsNodup :
        (PeriodicThreeSATThree.sourceVariables source).Nodup := by
      unfold PeriodicThreeSATThree.sourceVariables
      exact List.nodup_dedup _
    apply atomsNodup.imp
    intro first second different occurrence firstMember secondMember
    apply different
    exact (copy_fst first firstMember).symm.trans
      (copy_fst second secondMember)

/-- There are exactly nine output copies per distinct source variable. -/
theorem allCopies_length {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (allCopies source).length =
      PeriodicCNF.FormulaShapeFixedEight.copiesPerVariable *
        source.variableOccurrences.dedup.length := by
  let atoms := PeriodicThreeSATThree.sourceVariables source
  have blocks :
      (atoms.flatMap copies).length =
        PeriodicCNF.FormulaShapeFixedEight.copiesPerVariable *
          atoms.length := by
    induction atoms with
    | nil => rfl
    | cons atom atoms induction =>
        simp only [List.flatMap_cons, List.length_append,
          List.length_cons, copies_length]
        rw [induction]
        unfold PeriodicCNF.FormulaShapeFixedEight.copiesPerVariable
        omega
  unfold allCopies
  rw [blocks]
  have atomsEq : atoms = source.variableOccurrences.dedup :=
    sourceVariables_eq_variableOccurrences_dedup source
  rw [atomsEq]

/-- Every member of a nonempty cycle-copy list occurs in its implication
cycle. -/
theorem mem_cycleClauses_variableOccurrences_of_mem
    {Variable : Type*} [DecidableEq Variable]
    (cycleCopies : List (ThreeOccurrenceVariable Variable))
    {selected : ThreeOccurrenceVariable Variable}
    (member : selected ∈ cycleCopies) :
    selected ∈ PeriodicCNF.variableOccurrences
      ⟨PeriodicThreeSATThree.cycleClauses cycleCopies⟩ := by
  cases cycleCopies with
  | nil => simp at member
  | cons first rest =>
      apply List.count_pos_iff.mp
      rw [PeriodicThreeSATThree.cycleClauses,
        PeriodicThreeSATThree.cycleFrom_count]
      have positive : 0 < (first :: rest).count selected :=
        List.count_pos_iff.mpr member
      omega

/-- Every enumerated copy occurs in the cycle-clause suffix. -/
theorem allCopies_subset_cycleOccurrences
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    allCopies source ⊆
      PeriodicCNF.variableOccurrences
        ⟨allCycleClauses source⟩ := by
  intro selected member
  simp only [allCopies, List.mem_flatMap] at member
  rcases member with ⟨atom, atomMember, copyMember⟩
  unfold allCycleClauses
  rw [PeriodicThreeSATThree.variableOccurrences_flatMap,
    List.mem_flatMap]
  exact ⟨atom, atomMember,
    mem_cycleClauses_variableOccurrences_of_mem
      (copies atom) copyMember⟩

/-- Conversely, every cycle-clause occurrence is one of the enumerated
copies. -/
theorem cycleOccurrences_subset_allCopies
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    PeriodicCNF.variableOccurrences
        ⟨allCycleClauses source⟩ ⊆
      allCopies source := by
  intro selected member
  unfold allCycleClauses at member
  rw [PeriodicThreeSATThree.variableOccurrences_flatMap,
    List.mem_flatMap] at member
  rcases member with ⟨atom, atomMember, cycleMember⟩
  rw [allCopies, List.mem_flatMap]
  exact ⟨atom, atomMember,
    PeriodicThreeSATThree.cycleClauses_variableOccurrences_subset
      (copies atom) cycleMember⟩

/-- Every occurrence in a copied source clause belongs to the appropriate
nine-copy block. -/
theorem occurrenceClauses_variableOccurrences_subset_allCopies
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (occurrencePorts : OccurrencePorts) :
    PeriodicCNF.variableOccurrences
        ⟨occurrenceClauses source occurrencePorts⟩ ⊆
      allCopies source := by
  intro selected member
  rw [occurrenceClauses_variableOccurrences] at member
  unfold selectedCopies at member
  rcases List.mem_map.mp member with
    ⟨tagged, taggedMember, rfl⟩
  rw [allCopies, List.mem_flatMap]
  exact ⟨tagged.1.atom,
    PeriodicThreeSATThree.sourceVariables_mem source taggedMember,
    copy_mem_copies tagged.1.atom
      (occurrencePorts.port tagged.2.1 tagged.2.2)⟩

/-- The fixed-eight formula's distinct variables have exactly the explicit
nine-copy enumeration's members. -/
theorem formula_variableOccurrences_mem_iff_allCopies
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (occurrencePorts : OccurrencePorts)
    (selected : ThreeOccurrenceVariable Variable) :
    selected ∈ PeriodicCNF.variableOccurrences
        (formula source occurrencePorts) ↔
      selected ∈ allCopies source := by
  change selected ∈ PeriodicCNF.variableOccurrences
      ⟨occurrenceClauses source occurrencePorts ++
        allCycleClauses source⟩ ↔ _
  rw [PeriodicThreeSATThree.variableOccurrences_append,
    List.mem_append]
  constructor
  · rintro (occurrenceMember | cycleMember)
    · exact occurrenceClauses_variableOccurrences_subset_allCopies
        source occurrencePorts occurrenceMember
    · exact cycleOccurrences_subset_allCopies source cycleMember
  · intro member
    exact Or.inr (allCopies_subset_cycleOccurrences source member)

/-- Fixed-eight splitting creates exactly nine distinct copies for every
distinct source variable. -/
@[simp] theorem formula_variableOccurrences_dedup_length
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (occurrencePorts : OccurrencePorts) :
    (PeriodicCNF.variableOccurrences
      (formula source occurrencePorts)).dedup.length =
      PeriodicCNF.FormulaShapeFixedEight.copiesPerVariable *
        source.variableOccurrences.dedup.length := by
  have perm :
      (PeriodicCNF.variableOccurrences
          (formula source occurrencePorts)).dedup.Perm
        (allCopies source) :=
    (List.perm_ext_iff_of_nodup
      (List.nodup_dedup _) (allCopies_nodup source)).mpr fun selected => by
        rw [List.mem_dedup,
          formula_variableOccurrences_mem_iff_allCopies]
  calc
    (PeriodicCNF.variableOccurrences
        (formula source occurrencePorts)).dedup.length =
        (allCopies source).length := perm.length_eq
    _ = PeriodicCNF.FormulaShapeFixedEight.copiesPerVariable *
          source.variableOccurrences.dedup.length :=
      allCopies_length source

end PeriodicEightOccurrenceSplit
end LeanTrominoes
