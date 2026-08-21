/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceMetadataLocalRanks
import LeanTrominoes.PeriodicCNFRenamingData

/-! # Presentation streams under atom renaming -/

namespace LeanTrominoes

namespace PeriodicLiteral

@[simp] theorem rename_atom {Source Target : Type*}
    (variableMap : Source → Target) (literal : PeriodicLiteral Source) :
    (literal.rename variableMap).atom = variableMap literal.atom := rfl

@[simp] theorem rename_offset {Source Target : Type*}
    (variableMap : Source → Target) (literal : PeriodicLiteral Source) :
    (literal.rename variableMap).offset = literal.offset := rfl

@[simp] theorem rename_value {Source Target : Type*}
    (variableMap : Source → Target) (literal : PeriodicLiteral Source) :
    (literal.rename variableMap).value = literal.value := rfl

end PeriodicLiteral

namespace PeriodicCNF

@[simp] theorem renameClause_length {Source Target : Type*}
    (variableMap : Source → Target) (clause : PeriodicClause Source) :
    (renameClause variableMap clause).length = clause.length := by
  simp [renameClause]

@[simp] theorem rename_clauses_length {Source Target : Type*}
    (variableMap : Source → Target) (formula : PeriodicCNF Source) :
    (rename variableMap formula).clauses.length = formula.clauses.length := by
  simp [rename]

/-- Renaming maps the flattened occurrence stream pointwise. -/
theorem variableOccurrences_rename {Source Target : Type*}
    (variableMap : Source → Target) (formula : PeriodicCNF Source) :
    variableOccurrences (rename variableMap formula) =
      (variableOccurrences formula).map variableMap := by
  unfold variableOccurrences rename
  rw [List.flatMap_map, List.map_flatMap]
  apply List.flatMap_congr
  intro clause clauseMember
  simp [renameClause, PeriodicLiteral.rename, List.map_map,
    Function.comp_def]

/-- Renaming maps incidence metadata pointwise without changing either stable
presentation index. -/
theorem incidencesWithMetadata_rename {Source Target : Type*}
    (variableMap : Source → Target) (formula : PeriodicCNF Source) :
    incidencesWithMetadata (rename variableMap formula) =
      (incidencesWithMetadata formula).map
        (CNFIncidence.rename variableMap) := by
  rw [incidencesWithMetadata_eq_blocks,
    incidencesWithMetadata_eq_blocks]
  unfold rename
  rw [List.zipIdx_map, List.flatMap_map, List.map_flatMap]
  apply List.flatMap_congr
  intro taggedClause taggedClauseMember
  rcases taggedClause with ⟨clause, clauseIndex⟩
  simp only [Prod.map, id_eq]
  unfold incidenceMetadataBlock renameClause
  rw [List.zipIdx_map, List.map_map, List.map_map]
  apply List.map_congr_left
  intro taggedLiteral taggedLiteralMember
  rcases taggedLiteral with ⟨literal, literalIndex⟩
  rfl

end PeriodicCNF

namespace CNFIncidence

@[simp] theorem rename_clauseIndex {Source Target : Type*}
    (variableMap : Source → Target) (incidence : CNFIncidence Source) :
    (incidence.rename variableMap).clauseIndex = incidence.clauseIndex := rfl

@[simp] theorem rename_literalIndex {Source Target : Type*}
    (variableMap : Source → Target) (incidence : CNFIncidence Source) :
    (incidence.rename variableMap).literalIndex = incidence.literalIndex := rfl

@[simp] theorem rename_literal_atom {Source Target : Type*}
    (variableMap : Source → Target) (incidence : CNFIncidence Source) :
    (incidence.rename variableMap).literal.atom =
      variableMap incidence.literal.atom := rfl

end CNFIncidence

end LeanTrominoes
