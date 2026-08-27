/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNinePolarityRouteTailData
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteTailRecordBatchSemantics

/-! # Flat clause inputs for Figure 9 polarity route tails -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeFigureNinePolarityRouteTailRecord

open FormulaShapeDirectionOrdering
open FormulaShapeFigureNinePolarityRouteTail
open PeriodicCNFStripReduction
open PeriodicCNFStripReduction.HorizontalRoutedRouteTailRecord

/-- Pair every directed source clause with the next dynamic tail table.
Variable markers consume no table because they generate no Figure 9 clause. -/
def sourceClauses :
    List FormulaShapeDirectionOrdering.Token →
      List (List (List AxisDirection)) →
        List (DirectedClauseProfile × List (List AxisDirection))
  | [], _ => []
  | .variable :: source, tailTables =>
      sourceClauses source tailTables
  | .clause profile :: source, tailTables =>
      (profile, tailTables.headD []) ::
        sourceClauses source tailTables.tail

/-- Number of clause descriptors that consume rows from the aligned dynamic
tail-table stream. -/
def sourceClauseCount :
    List FormulaShapeDirectionOrdering.Token → Nat
  | [] => 0
  | .variable :: source => sourceClauseCount source
  | .clause _ :: source => 1 + sourceClauseCount source

@[simp] theorem sourceClauseCount_append
    (first second : List FormulaShapeDirectionOrdering.Token) :
    sourceClauseCount (first ++ second) =
      sourceClauseCount first + sourceClauseCount second := by
  induction first with
  | nil => simp [sourceClauseCount]
  | cons token first induction =>
      cases token <;> simp [sourceClauseCount, induction, Nat.add_assoc]

@[simp] theorem sourceClauseCount_map_clause
    (profiles : List DirectedClauseProfile) :
    sourceClauseCount
        (profiles.map FormulaShapeDirectionOrdering.Token.clause) =
      profiles.length := by
  induction profiles with
  | nil => rfl
  | cons profile profiles induction =>
      simp [sourceClauseCount, induction]
      omega

@[simp] theorem sourceClauseCount_map_clause_apply {Value : Type}
    (values : List Value) (profile : Value → DirectedClauseProfile) :
    sourceClauseCount
        (values.map fun value =>
          FormulaShapeDirectionOrdering.Token.clause (profile value)) =
      values.length := by
  induction values with
  | nil => rfl
  | cons value values induction =>
      simp [sourceClauseCount, induction]
      omega

@[simp] theorem sourceClauseCount_replicate_variable (count : Nat) :
    sourceClauseCount
        (List.replicate count FormulaShapeDirectionOrdering.Token.variable) =
      0 := by
  induction count with
  | zero => rfl
  | succ count induction =>
      simp [List.replicate_succ, sourceClauseCount, induction]

/-- A phase boundary in the descriptor stream induces the same boundary in
the paired clause/tail records, provided the first tail phase has exactly one
row for each clause descriptor. -/
theorem sourceClauses_append
    (first second : List FormulaShapeDirectionOrdering.Token)
    (firstTails secondTails : List (List (List AxisDirection)))
    (firstLength : firstTails.length = sourceClauseCount first) :
    sourceClauses (first ++ second) (firstTails ++ secondTails) =
      sourceClauses first firstTails ++
        sourceClauses second secondTails := by
  induction first generalizing firstTails with
  | nil =>
      cases firstTails with
      | nil => simp [sourceClauses]
      | cons firstTail firstTails =>
          simp [sourceClauseCount] at firstLength
  | cons token first induction =>
      cases token with
      | «variable» =>
          simpa [sourceClauses, sourceClauseCount] using
            induction firstTails firstLength
      | clause profile =>
          cases firstTails with
          | nil =>
              simp [sourceClauseCount] at firstLength
              omega
          | cons firstTail firstTails =>
              have tailLength :
                  firstTails.length = sourceClauseCount first := by
                simp [sourceClauseCount] at firstLength
                omega
              simp [sourceClauses, induction firstTails tailLength]

/-- Canonical finite-alphabet clause records before the bounded indexed
tail expansion. -/
def sourceRecordTokens
    (source : List FormulaShapeDirectionOrdering.Token)
    (tailTables : List (List (List AxisDirection))) :
    List HorizontalRoutedRouteTailRecord.Token :=
  clauseRecords (sourceClauses source tailTables)

@[simp] theorem sourceRecordTokens_replicate_variable
    (count : Nat) (tailTables : List (List (List AxisDirection))) :
    sourceRecordTokens
        (List.replicate count FormulaShapeDirectionOrdering.Token.variable)
        tailTables = [] := by
  induction count generalizing tailTables with
  | zero => rfl
  | succ count induction =>
      simpa [List.replicate_succ, sourceRecordTokens, sourceClauses] using
        induction tailTables

/-- Flat clause-record serialization respects every aligned descriptor/tail
phase boundary. -/
@[simp] theorem sourceRecordTokens_append
    (first second : List FormulaShapeDirectionOrdering.Token)
    (firstTails secondTails : List (List (List AxisDirection)))
    (firstLength : firstTails.length = sourceClauseCount first) :
    sourceRecordTokens (first ++ second) (firstTails ++ secondTails) =
      sourceRecordTokens first firstTails ++
        sourceRecordTokens second secondTails := by
  unfold sourceRecordTokens clauseRecords
  rw [sourceClauses_append first second firstTails secondTails firstLength,
    List.flatMap_append]

/-- Expanding the flat clause inputs reconstructs the established aligned
header/tail record stream for the entire direction-aware formula shape. -/
@[simp] theorem batchedRecords_sourceRecordTokens
    (source : List FormulaShapeDirectionOrdering.Token)
    (tailTables : List (List (List AxisDirection))) :
    batchedRecords (sourceRecordTokens source tailTables) =
      FormulaShapeFigureNinePolarityRouteTail.sourceRecords
        source tailTables := by
  unfold sourceRecordTokens
  rw [batchedRecords_clauseRecords]
  induction source generalizing tailTables with
  | nil => rfl
  | cons token source induction =>
      cases token with
      | «variable» =>
          simpa [sourceClauses,
            FormulaShapeFigureNinePolarityRouteTail.sourceRecords] using
            induction tailTables
      | clause profile =>
          simp [sourceClauses,
            FormulaShapeFigureNinePolarityRouteTail.sourceRecords,
            induction]

end FormulaShapeFigureNinePolarityRouteTailRecord
end PeriodicCNF
end LeanTrominoes
