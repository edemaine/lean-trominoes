/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerTime
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderEndpointDirections
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderTailData

/-! # Streaming variable occurrence data with the completed endpoint -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction.HorizontalRoutedVariableOccurrence

open Computability Turing
open HorizontalRoutedRouteHeaderTail

abbrev State := Option (Header × Option AxisDirection)
abbrev Output := HorizontalRoutedRouteHeader.OccurrenceData

/-- Remember the header and only the most recent dynamic-tail direction.
Emit the completed variable-side record at the explicit end marker. -/
def transition (state : State) : Token → State × List Output
  | .header header => (some (header, none), [])
  | .tailDirection direction =>
      (state.map (fun value => (value.1, some direction)), [])
  | .recordEnd =>
      (none, state.toList.map fun value =>
        HorizontalRoutedRouteHeader.completeOccurrenceData value.1 value.2.toList)

def finish (_ : State) : List Output := []

def output (input : List Token) : List Output :=
  FiniteStateTransducer.output none transition finish input

/-- The stored endpoint summary ranges over a fixed finite alphabet. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime id id output :=
  FiniteStateTransducer.computableInPolyTime none transition finish

private theorem scan_tailRecord (header : Header)
    (previous : Option AxisDirection) (tail : List AxisDirection) :
    FiniteStateTransducer.scan transition (some (header, previous))
      (tail.map Token.tailDirection ++ [.recordEnd]) =
      (none, [HorizontalRoutedRouteHeader.completeOccurrenceData header
        ((tail.getLast?).or previous).toList]) := by
  induction tail generalizing previous with
  | nil => simp [FiniteStateTransducer.scan, transition]
  | cons direction tail induction =>
      simp only [List.map_cons, List.cons_append, FiniteStateTransducer.scan,
        transition, Option.map_some]
      rw [induction]
      cases tail <;> simp [List.getLast?_cons]

private theorem scan_record (state : State) (header : Header)
    (tail : List AxisDirection) :
    FiniteStateTransducer.scan transition state (record header tail) =
      (none, [HorizontalRoutedRouteHeader.completeOccurrenceData header tail]) := by
  simp only [record, List.cons_append, FiniteStateTransducer.scan, transition]
  rw [scan_tailRecord]
  simp only [Option.or_none, List.nil_append]
  rw [← HorizontalRoutedRouteHeader.completeOccurrenceData_eq_lastTail]

theorem output_record_append (header : Header) (tail : List AxisDirection)
    (remaining : List Token) :
    output (record header tail ++ remaining) =
      HorizontalRoutedRouteHeader.completeOccurrenceData header tail :: output remaining := by
  unfold output FiniteStateTransducer.output
  rw [FiniteStateTransducer.scan_append, scan_record]
  simp [finish]

/-- Every complete input record produces its exact variable-side endpoint
data, including the last direction of an arbitrarily long tail. -/
@[simp] theorem output_records (pairs : List (Header × List AxisDirection)) :
    output (records pairs) = pairs.map fun pair =>
      HorizontalRoutedRouteHeader.completeOccurrenceData pair.1 pair.2 := by
  induction pairs with
  | nil => rfl
  | cons pair pairs induction =>
      change output (record pair.1 pair.2 ++ records pairs) = _
      rw [output_record_append, induction]
      rfl

end LeanTrominoes.PeriodicCNFStripReduction.HorizontalRoutedVariableOccurrence

end
