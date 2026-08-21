/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceMetadataAppend
import LeanTrominoes.PeriodicThreeSATThreeOccurrenceIncidenceSemantics
import LeanTrominoes.PeriodicThreeSATThreeOccurrences
import LeanTrominoes.PeriodicThreeSATThreeSize

/-! # Exact copied prefixes of the occurrence-split formula -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

/-- The first `n` metadata records of the complete split formula are exactly
the pointwise lifted source incidences. -/
theorem formula_incidencesWithMetadata_take_sourceCount
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (PeriodicCNF.incidencesWithMetadata (formula source)).take
        (PeriodicCNF.presentationLiteralCount source) =
      occurrenceIncidences source := by
  have firstLength :
      (PeriodicCNF.incidencesWithMetadata
        (PeriodicCNF.mk (occurrenceClauses source))).length =
          PeriodicCNF.presentationLiteralCount source := by
    rw [incidencesWithMetadata_occurrenceClauses]
    exact occurrenceIncidences_length source
  change
    (PeriodicCNF.incidencesWithMetadata
      (PeriodicCNF.mk
        (occurrenceClauses source ++ allCycleClauses source))).take
          (PeriodicCNF.presentationLiteralCount source) = _
  calc
    _ = (PeriodicCNF.incidencesWithMetadata
          (PeriodicCNF.mk
            (occurrenceClauses source ++ allCycleClauses source))).take
          (PeriodicCNF.incidencesWithMetadata
            (PeriodicCNF.mk (occurrenceClauses source))).length := by
        rw [firstLength]
    _ = PeriodicCNF.incidencesWithMetadata
          (PeriodicCNF.mk (occurrenceClauses source)) :=
      PeriodicCNF.incidencesWithMetadata_append_take_prefix _ _
    _ = occurrenceIncidences source :=
      incidencesWithMetadata_occurrenceClauses source

/-- The first `n` variable occurrences of the complete split formula are the
pairwise-distinct occurrence copies from the copied source clauses. -/
theorem formula_variableOccurrences_take_sourceCount
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (PeriodicCNF.variableOccurrences (formula source)).take
        (PeriodicCNF.presentationLiteralCount source) =
      allOccurrenceVariables source := by
  have originalsLength :
      (allOccurrenceVariables source).length =
        PeriodicCNF.presentationLiteralCount source := by
    simp [allOccurrenceVariables]
  have occurrencesAppend :
      PeriodicCNF.variableOccurrences (formula source) =
        allOccurrenceVariables source ++
          PeriodicCNF.variableOccurrences
            (PeriodicCNF.mk (allCycleClauses source)) := by
    unfold formula
    rw [variableOccurrences_append,
      occurrenceClauses_variableOccurrences]
  rw [occurrencesAppend, ← originalsLength]
  simp

end PeriodicThreeSATThree
end LeanTrominoes
