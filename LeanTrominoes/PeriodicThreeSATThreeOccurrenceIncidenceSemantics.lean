/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.IndexedListMapIndices
import LeanTrominoes.PeriodicThreeSATThreeOccurrenceIncidenceData

/-! # Correctness of copied occurrence incidences -/

namespace LeanTrominoes

namespace PeriodicThreeSATThree

/-- Computing metadata after copying all source clauses gives exactly the
pointwise lifted source metadata stream. -/
theorem incidencesWithMetadata_occurrenceClauses
    {Variable : Type*} (source : PeriodicCNF Variable) :
    PeriodicCNF.incidencesWithMetadata
        (PeriodicCNF.mk (occurrenceClauses source)) =
      occurrenceIncidences source := by
  have clauseIndices :
      (occurrenceClauses source).zipIdx =
        source.clauses.zipIdx.map fun taggedClause =>
          (occurrenceClause taggedClause.2 taggedClause.1,
            taggedClause.2) := by
    unfold occurrenceClauses
    simpa only using
      (List.indexedMap_zipIdx source.clauses
        (fun clause clauseIndex =>
          occurrenceClause clauseIndex clause) 0)
  unfold occurrenceIncidences PeriodicCNF.incidencesWithMetadata
  rw [List.map_flatMap]
  rw [clauseIndices]
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro taggedClause taggedClauseMember
  have literalIndices :
      (occurrenceClause taggedClause.2 taggedClause.1).zipIdx =
        taggedClause.1.zipIdx.map fun taggedLiteral =>
          (occurrenceLiteral taggedClause.2 taggedLiteral.2
            taggedLiteral.1, taggedLiteral.2) := by
    unfold occurrenceClause
    simpa only using
      (List.indexedMap_zipIdx taggedClause.1
        (fun literal literalIndex =>
          occurrenceLiteral taggedClause.2 literalIndex literal) 0)
  rw [literalIndices]
  simp only [List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro taggedLiteral taggedLiteralMember
  unfold occurrenceIncidence
  rfl

end PeriodicThreeSATThree
end LeanTrominoes
