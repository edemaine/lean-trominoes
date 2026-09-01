/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderOccurrenceData
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderTailData

/-! # Streaming finite occurrence data from routed Figure 9 records -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction
namespace HorizontalRoutedRouteHeaderOccurrence

open Computability Turing

abbrev InputToken := HorizontalRoutedRouteHeaderTail.Token
abbrev Output := HorizontalRoutedRouteHeader.OccurrenceData

/-- Retain exactly the finite occurrence record stored at a route header. -/
def tokenBlock : InputToken → List Output
  | .header header => [HorizontalRoutedRouteHeader.occurrenceData header]
  | .tailDirection _ | .recordEnd => []

/-- One finite occurrence record per delimited routed Figure 9 record. -/
def output (input : List InputToken) : List Output :=
  input.flatMap tokenBlock

@[simp] theorem output_append (first second : List InputToken) :
    output (first ++ second) = output first ++ output second := by
  simp [output]

/-- Header projection is a fixed finite block transducer. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime id id output :=
  FiniteBlockTransducer.computableInPolyTime tokenBlock

@[simp] theorem output_record
    (header : HorizontalRoutedRouteHeaderTail.Header)
    (sourceTailDirections : List AxisDirection) :
    output
        (HorizontalRoutedRouteHeaderTail.record
          header sourceTailDirections) =
      [HorizontalRoutedRouteHeader.occurrenceData header] := by
  simp [output, tokenBlock, HorizontalRoutedRouteHeaderTail.record]

@[simp] theorem output_records
    (values : List
      (HorizontalRoutedRouteHeaderTail.Header × List AxisDirection)) :
    output (HorizontalRoutedRouteHeaderTail.records values) =
      values.map fun value =>
        HorizontalRoutedRouteHeader.occurrenceData value.1 := by
  induction values with
  | nil => rfl
  | cons value values induction =>
      change output
          (HorizontalRoutedRouteHeaderTail.record value.1 value.2 ++
            HorizontalRoutedRouteHeaderTail.records values) = _
      rw [output_append, output_record, induction]
      rfl

end HorizontalRoutedRouteHeaderOccurrence
end PeriodicCNFStripReduction
end LeanTrominoes

end
