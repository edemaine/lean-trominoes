/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalTypedElementDegreePattern
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMOccurrenceCorrespondence

/-! # Clause-order semantics of typed variable-element degrees -/

noncomputable section

set_option maxHeartbeats 800000

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF
open PeriodicPlanarOneInThreeToThreeDM

private def taggedVariableElementDegreeBlock
    {Variable : Type*}
    (tagged : PeriodicPlanarOneInThreeToThreeDM.TaggedOccurrence Variable) :
    List Nat :=
  match connectorKindOfLiteralIndex tagged.2.2 with
  | .fixedRed => [2, 2, 2]
  | .fixedGreen | .fixedBlue => [2]

private def clauseVariableElementDegrees (clauseLength : Nat) : List Nat :=
  if clauseLength = 3 then [2, 2, 2, 2, 2] else [2, 2, 2, 2]

private theorem horizontalTypedVariableElementDegrees_eq_entryFlatMap
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    horizontalTypedVariableElementDegrees source =
      (occurrenceEntries source).flatMap fun entry =>
        horizontalTypedVariableElementDegreeBlock source entry.1 entry.2 := by
  simp only [horizontalTypedVariableElementDegrees, occurrenceEntries,
    List.flatMap_assoc, List.flatMap_map]

private theorem horizontalTypedEntryDegreeBlock_eq_tagged
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (entry : Variable × PeriodicOneInThreeToThreeDM.OccurrenceSlot)
    (tagged : PeriodicPlanarOneInThreeToThreeDM.TaggedOccurrence Variable)
    (lookup : PeriodicPlanarOneInThreeToThreeDM.occurrenceAt
      source entry.1 entry.2 = some tagged) :
    horizontalTypedVariableElementDegreeBlock source entry.1 entry.2 =
      taggedVariableElementDegreeBlock tagged := by
  unfold PeriodicPlanarOneInThreeToThreeDM.occurrenceAt at lookup
  unfold horizontalTypedVariableElementDegreeBlock
    occurrenceConnectorKind occurrenceLiteralIndex
    PeriodicPlanarOneInThreeToThreeDM.occurrenceAt
  rw [lookup]
  rfl

private theorem horizontalTypedEntryDegreeBlocks_eq_enumeration
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (occurrenceEntries source).flatMap (fun entry =>
        horizontalTypedVariableElementDegreeBlock source entry.1 entry.2) =
      (occurrenceEnumeration source).flatMap
        taggedVariableElementDegreeBlock := by
  unfold occurrenceEnumeration
  let entries := occurrenceEntries source
  have valid : ∀ entry ∈ entries, ∃ tagged,
      PeriodicPlanarOneInThreeToThreeDM.occurrenceAt
        source entry.1 entry.2 = some tagged := by
    intro entry entryMember
    exact occurrenceAt_exists_of_entry_mem source entry entryMember
  change entries.flatMap _ = (entries.filterMap _).flatMap _
  revert valid
  induction entries with
  | nil => intro _valid; rfl
  | cons entry entries induction =>
      intro valid
      rcases valid entry List.mem_cons_self with ⟨tagged, lookup⟩
      have tailValid : ∀ other ∈ entries, ∃ output,
          PeriodicPlanarOneInThreeToThreeDM.occurrenceAt
            source other.1 other.2 = some output := by
        intro other otherMember
        exact valid other (List.mem_cons_of_mem entry otherMember)
      simp only [List.flatMap_cons, List.filterMap_cons, lookup,
        List.flatMap_cons]
      rw [horizontalTypedEntryDegreeBlock_eq_tagged
        source entry tagged lookup]
      exact congrArg (taggedVariableElementDegreeBlock tagged ++ ·)
        (induction tailValid)

private theorem taggedClauseVariableElementDegrees_eq
    {Variable : Type*} (clause : PeriodicClause Variable)
    (clauseIndex : Nat)
    (arity : clause.length = 2 ∨ clause.length = 3) :
    (clause.zipIdx.map fun (literal, literalIndex) =>
      (literal, clauseIndex, literalIndex)).flatMap
        taggedVariableElementDegreeBlock =
      clauseVariableElementDegrees clause.length := by
  rcases arity with lengthTwo | lengthThree
  · rcases List.length_eq_two.mp lengthTwo with ⟨first, second, rfl⟩
    rfl
  · rcases List.length_eq_three.mp lengthThree with
      ⟨first, second, third, rfl⟩
    rfl

private theorem taggedLiteralsVariableElementDegrees_eq_clauseFlatMap
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree source) :
    (PeriodicThreeSATThree.taggedLiterals source).flatMap
        taggedVariableElementDegreeBlock =
      source.clauses.flatMap fun clause =>
        clauseVariableElementDegrees clause.length := by
  unfold PeriodicThreeSATThree.taggedLiterals
  rw [List.flatMap_assoc]
  rw [← PeriodicCNF.zipIdx_flatMap_fst
    (fun clause => clauseVariableElementDegrees clause.length)
    source.clauses 0]
  apply List.flatMap_congr
  intro taggedClause taggedClauseMember
  have clauseMember : taggedClause.1 ∈ source.clauses := by
    have mappedMember : taggedClause.1 ∈
        (source.clauses.zipIdx 0).map Prod.fst :=
      List.mem_map_of_mem taggedClauseMember
    simpa only [List.zipIdx_map_fst] using mappedMember
  exact taggedClauseVariableElementDegrees_eq
    taggedClause.1 taggedClause.2 (arity taggedClause.1 clauseMember)

private theorem horizontalTypedVariableElementDegrees_all_two
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    ∀ degree ∈ horizontalTypedVariableElementDegrees source,
      degree = 2 := by
  intro degree degreeMember
  unfold horizontalTypedVariableElementDegrees at degreeMember
  simp only [List.mem_flatMap] at degreeMember
  obtain ⟨atom, _atomMember, degreeMember⟩ := degreeMember
  obtain ⟨slot, _slotMember, degreeMember⟩ := degreeMember
  cases kindEq : occurrenceConnectorKind source atom slot <;>
    simp [horizontalTypedVariableElementDegreeBlock, kindEq] at degreeMember <;>
    exact degreeMember

private theorem clauseVariableElementDegrees_all_two
    {Variable : Type*} (source : PeriodicCNF Variable) :
    ∀ degree ∈ source.clauses.flatMap (fun clause =>
        clauseVariableElementDegrees clause.length),
      degree = 2 := by
  intro degree degreeMember
  simp only [List.mem_flatMap] at degreeMember
  obtain ⟨clause, _clauseMember, degreeMember⟩ := degreeMember
  unfold clauseVariableElementDegrees at degreeMember
  split at degreeMember <;> simp_all

/-- Although variable modules use variable-major order, their degree column
is the same all-two list obtained clause by clause: four entries for a binary
clause and five for a ternary clause. -/
theorem horizontalTypedVariableElementDegrees_eq_clauseFlatMap
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (occurrences : source.OccurrencesAtMost 3)
    (arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree source) :
    horizontalTypedVariableElementDegrees source =
      source.clauses.flatMap fun clause =>
        if clause.length = 3 then
          [2, 2, 2, 2, 2]
        else
          [2, 2, 2, 2] := by
  let target := source.clauses.flatMap fun clause =>
    clauseVariableElementDegrees clause.length
  have enumerationPerm :=
    occurrenceEnumeration_perm_taggedLiterals source occurrences
  have blockPerm :
      List.Perm
        ((occurrenceEnumeration source).flatMap
          taggedVariableElementDegreeBlock)
        ((PeriodicThreeSATThree.taggedLiterals source).flatMap
          taggedVariableElementDegreeBlock) :=
    enumerationPerm.flatMap fun tagged _ => List.Perm.refl _
  have lengthEq :
      (horizontalTypedVariableElementDegrees source).length =
        target.length := by
    rw [horizontalTypedVariableElementDegrees_eq_entryFlatMap,
      horizontalTypedEntryDegreeBlocks_eq_enumeration]
    exact blockPerm.length_eq.trans
      (congrArg List.length
        (taggedLiteralsVariableElementDegrees_eq_clauseFlatMap
          source arity))
  calc
    horizontalTypedVariableElementDegrees source =
        List.replicate
          (horizontalTypedVariableElementDegrees source).length 2 :=
      List.eq_replicate_length.mpr
        (horizontalTypedVariableElementDegrees_all_two source)
    _ = List.replicate target.length 2 := by rw [lengthEq]
    _ = target :=
      (List.eq_replicate_length.mpr
        (clauseVariableElementDegrees_all_two source)).symm

end LeanTrominoes.PeriodicCNFStripReduction
