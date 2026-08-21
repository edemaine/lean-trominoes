/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFRenamingStreams
import LeanTrominoes.PeriodicThreeSATThree

/-! # Occurrence-copy data under injective atom renaming -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

/-- Lift an atom map to the positional occurrence-copy type. -/
def renameOccurrence {Source Target : Type*} (variableMap : Source → Target)
    (copy : ThreeOccurrenceVariable Source) :
    ThreeOccurrenceVariable Target :=
  (variableMap copy.1, copy.2.1, copy.2.2)

theorem renameOccurrence_injective
    {Source Target : Type*} (variableMap : Source → Target)
    (injective : Function.Injective variableMap) :
    Function.Injective (renameOccurrence variableMap) := by
  intro first second equal
  apply Prod.ext
  · exact injective (congrArg
      (fun copy : ThreeOccurrenceVariable Target => copy.1) equal)
  · exact congrArg
      (fun copy : ThreeOccurrenceVariable Target => copy.2) equal

/-- Rename the atom inside one indexed source literal. -/
def renameTaggedLiteral {Source Target : Type*}
    (variableMap : Source → Target)
    (tagged : PeriodicLiteral Source × Nat × Nat) :
    PeriodicLiteral Target × Nat × Nat :=
  (tagged.1.rename variableMap, tagged.2.1, tagged.2.2)

/-- The stable clause/literal tags are unchanged by formula renaming. -/
theorem taggedLiterals_rename
    {Source Target : Type*} (variableMap : Source → Target)
    (source : PeriodicCNF Source) :
    taggedLiterals (source.rename variableMap) =
      (taggedLiterals source).map (renameTaggedLiteral variableMap) := by
  unfold taggedLiterals PeriodicCNF.rename
  rw [List.zipIdx_map, List.flatMap_map, List.map_flatMap]
  apply List.flatMap_congr
  intro taggedClause taggedClauseMember
  rcases taggedClause with ⟨clause, clauseIndex⟩
  simp only [Prod.map, id_eq]
  unfold PeriodicCNF.renameClause
  rw [List.zipIdx_map, List.map_map, List.map_map]
  apply List.map_congr_left
  intro taggedLiteral taggedLiteralMember
  rcases taggedLiteral with ⟨literal, literalIndex⟩
  rfl

/-- First-occurrence source-variable order is mapped pointwise by an
injective rename. -/
theorem sourceVariables_rename_of_injective
    {Source Target : Type*}
    [DecidableEq Source] [DecidableEq Target]
    (variableMap : Source → Target)
    (injective : Function.Injective variableMap)
    (source : PeriodicCNF Source) :
    sourceVariables (source.rename variableMap) =
      (sourceVariables source).map variableMap := by
  unfold sourceVariables
  rw [taggedLiterals_rename, List.map_map]
  have mapped :
      (taggedLiterals source).map
          ((fun tagged => tagged.1.atom) ∘
            renameTaggedLiteral variableMap) =
        ((taggedLiterals source).map
          (fun tagged => tagged.1.atom)).map variableMap := by
    rw [List.map_map]
    apply List.map_congr_left
    intro tagged taggedMember
    rfl
  rw [mapped, List.dedup_map_of_injective injective]

/-- Each occurrence-copy group is mapped pointwise by an injective rename. -/
theorem occurrenceVariables_rename_of_injective
    {Source Target : Type*}
    [DecidableEq Source] [DecidableEq Target]
    (variableMap : Source → Target)
    (injective : Function.Injective variableMap)
    (source : PeriodicCNF Source) (atom : Source) :
    occurrenceVariables (source.rename variableMap) (variableMap atom) =
      (occurrenceVariables source atom).map
        (renameOccurrence variableMap) := by
  unfold occurrenceVariables
  rw [taggedLiterals_rename, List.filterMap_map,
    List.map_filterMap]
  apply congrArg (fun scanner =>
    List.filterMap scanner (taggedLiterals source))
  funext tagged
  rcases tagged with ⟨literal, clauseIndex, literalIndex⟩
  by_cases same : literal.atom = atom
  · subst atom
    simp [renameTaggedLiteral, renameOccurrence,
      PeriodicLiteral.rename]
  · have mappedDifferent :
        variableMap literal.atom ≠ variableMap atom :=
      fun equal => same (injective equal)
    simp [renameTaggedLiteral,
      PeriodicLiteral.rename, same, mappedDifferent]

/-- Occurrence-copying commutes pointwise with atom renaming. -/
theorem occurrenceLiteral_rename
    {Source Target : Type*} (variableMap : Source → Target)
    (clauseIndex literalIndex : Nat) (literal : PeriodicLiteral Source) :
    occurrenceLiteral clauseIndex literalIndex
        (literal.rename variableMap) =
      (occurrenceLiteral clauseIndex literalIndex literal).rename
        (renameOccurrence variableMap) := by
  rfl

/-- One copied clause commutes with atom renaming. -/
theorem occurrenceClause_rename
    {Source Target : Type*} (variableMap : Source → Target)
    (clauseIndex : Nat) (clause : PeriodicClause Source) :
    occurrenceClause clauseIndex
        (PeriodicCNF.renameClause variableMap clause) =
      PeriodicCNF.renameClause (renameOccurrence variableMap)
        (occurrenceClause clauseIndex clause) := by
  unfold occurrenceClause PeriodicCNF.renameClause
  rw [List.zipIdx_map, List.map_map, List.map_map]
  apply List.map_congr_left
  intro taggedLiteral taggedLiteralMember
  rcases taggedLiteral with ⟨literal, literalIndex⟩
  rfl

/-- The complete copied-clause prefix commutes with atom renaming. -/
theorem occurrenceClauses_rename
    {Source Target : Type*} (variableMap : Source → Target)
    (source : PeriodicCNF Source) :
    occurrenceClauses (source.rename variableMap) =
      (occurrenceClauses source).map
        (PeriodicCNF.renameClause (renameOccurrence variableMap)) := by
  unfold occurrenceClauses PeriodicCNF.rename
  rw [List.zipIdx_map, List.map_map, List.map_map]
  apply List.map_congr_left
  intro taggedClause taggedClauseMember
  rcases taggedClause with ⟨clause, clauseIndex⟩
  exact occurrenceClause_rename variableMap clauseIndex clause

end PeriodicThreeSATThree
end LeanTrominoes
