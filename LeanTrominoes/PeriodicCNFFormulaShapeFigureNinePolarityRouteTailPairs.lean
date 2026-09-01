/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNinePolarityRouteTailData
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderOccurrenceCompiler

/-! # Explicit pair list underlying Figure 9 route-tail records -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeFigureNinePolarityRouteTail

open FormulaShapeDirectionOrdering
open PeriodicCNFStripReduction

/-- The header/tail pairs consumed by `sourceRecords`, with variable markers
discarded and one tail-table row consumed by each clause descriptor. -/
def sourcePairs :
    List FormulaShapeDirectionOrdering.Token →
      List (List (List AxisDirection)) →
        List (Header × List AxisDirection)
  | [], _ => []
  | .variable :: source, tailTables =>
      sourcePairs source tailTables
  | .clause profile :: source, tailTables =>
      sourceClausePairs profile (tailTables.headD []) ++
        sourcePairs source tailTables.tail

/-- The recursive token generator is exactly serialization of its explicit
header/tail pair list. -/
theorem sourceRecords_eq_records
    (descriptors : List FormulaShapeDirectionOrdering.Token)
    (tailTables : List (List (List AxisDirection))) :
    sourceRecords descriptors tailTables =
      HorizontalRoutedRouteHeaderTail.records
        (sourcePairs descriptors tailTables) := by
  induction descriptors generalizing tailTables with
  | nil => rfl
  | cons descriptor descriptors induction =>
      cases descriptor with
      | «variable» =>
          exact induction tailTables
      | clause profile =>
          unfold sourceRecords sourcePairs sourceClauseRecords
          rw [induction tailTables.tail]
          simp [HorizontalRoutedRouteHeaderTail.records]

/-- Projecting finite occurrence data from the record stream is ordinary
mapping over the same explicit pair list. -/
theorem occurrenceOutput_sourceRecords
    (descriptors : List FormulaShapeDirectionOrdering.Token)
    (tailTables : List (List (List AxisDirection))) :
    HorizontalRoutedRouteHeaderOccurrence.output
        (sourceRecords descriptors tailTables) =
      (sourcePairs descriptors tailTables).map fun pair =>
        HorizontalRoutedRouteHeader.occurrenceData pair.1 := by
  rw [sourceRecords_eq_records,
    HorizontalRoutedRouteHeaderOccurrence.output_records]

end FormulaShapeFigureNinePolarityRouteTail
end PeriodicCNF
end LeanTrominoes
