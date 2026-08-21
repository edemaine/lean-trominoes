/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceMetadataOccurrences
import LeanTrominoes.PeriodicThreeSATThreeOccurrenceIncidencePrefix

/-! # Variable order of copied occurrence incidences -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

/-- Erasing copied-incidence metadata yields exactly the distinct positional
occurrence-copy list. -/
theorem occurrenceIncidences_atoms
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (occurrenceIncidences source).map
        (fun incidence => incidence.literal.atom) =
      allOccurrenceVariables source := by
  calc
    (occurrenceIncidences source).map
        (fun incidence => incidence.literal.atom) =
      ((PeriodicCNF.incidencesWithMetadata (formula source)).take
          (PeriodicCNF.presentationLiteralCount source)).map
        (fun incidence => incidence.literal.atom) := by
          rw [formula_incidencesWithMetadata_take_sourceCount]
    _ = ((PeriodicCNF.incidencesWithMetadata (formula source)).map
          (fun incidence => incidence.literal.atom)).take
            (PeriodicCNF.presentationLiteralCount source) := by
      rw [List.map_take]
    _ = (PeriodicCNF.variableOccurrences (formula source)).take
          (PeriodicCNF.presentationLiteralCount source) := by
      rw [PeriodicCNF.incidencesWithMetadata_atoms]
    _ = allOccurrenceVariables source :=
      formula_variableOccurrences_take_sourceCount source

/-- Copied metadata records are pairwise distinct because their positional
variable endpoints are pairwise distinct. -/
theorem occurrenceIncidences_nodup
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (occurrenceIncidences source).Nodup := by
  apply List.Nodup.of_map
    (fun incidence => incidence.literal.atom)
  rw [occurrenceIncidences_atoms]
  exact allOccurrenceVariables_nodup source

end PeriodicThreeSATThree
end LeanTrominoes
