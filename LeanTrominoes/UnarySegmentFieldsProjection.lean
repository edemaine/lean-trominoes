/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.UnaryPointFieldsCompiler

/-! # Fixed-field projections of the native six-field segment table -/
noncomputable section
namespace LeanTrominoes.UnarySegmentFieldsProjection
open Computability Turing FiniteStateTransducer
open UnaryFieldEncoderMachine (Symbol unaryField unaryFields)

def next (index : Fin 6) : Fin 6 := ⟨(index.val + 1) % 6, Nat.mod_lt _ (by decide)⟩
def keep (coordinates : Bool) (index : Fin 6) : Bool :=
  if coordinates then decide (2 ≤ index.val) else decide (index.val = 0)

def transition (coordinates : Bool) (index : Fin 6) : Symbol → Fin 6 × List Symbol
  | .unit => (index, if keep coordinates index then [.unit] else [])
  | .delimiter => (next index, if keep coordinates index then [.delimiter] else [])

private theorem scan_units (coordinates : Bool) (index : Fin 6) (n : Nat) :
    scan (transition coordinates) index (List.replicate n Symbol.unit) =
      (index, if keep coordinates index then List.replicate n Symbol.unit else []) := by
  induction n with
  | zero => cases h : keep coordinates index <;> rfl
  | succ n ih =>
      cases h : keep coordinates index <;> simp [List.replicate_succ, scan, transition, h, ih]

private theorem scan_field (coordinates : Bool) (index : Fin 6) (n : Nat) :
    scan (transition coordinates) index (unaryField n) =
      (next index, if keep coordinates index then unaryField n else []) := by
  rw [unaryField, scan_append, scan_units]
  cases h : keep coordinates index <;> simp [scan, transition, h]

def fields (coordinates : Bool) (segment : IndexedGridSegment) : List Nat :=
  if coordinates then
    PeriodicGridDrawing.Arithmetic.pointFields segment.segment.start ++
      PeriodicGridDrawing.Arithmetic.pointFields segment.segment.finish
  else [segment.routeIndex]

private theorem scan_segment (coordinates : Bool) (segment : IndexedGridSegment) :
    scan (transition coordinates) 0 (unaryFields (PeriodicGridDrawing.Arithmetic.segmentFields segment)) =
      (0, unaryFields (fields coordinates segment)) := by
  cases coordinates <;>
    simp [PeriodicGridDrawing.Arithmetic.segmentFields, unaryFields,
      scan_append, scan_field, keep, next, fields,
      PeriodicGridDrawing.Arithmetic.pointFields]

private theorem scan_segments (coordinates : Bool) (segments : List IndexedGridSegment) :
    scan (transition coordinates) 0
      (unaryFields (segments.flatMap PeriodicGridDrawing.Arithmetic.segmentFields)) =
      (0, unaryFields (segments.flatMap (fields coordinates))) := by
  induction segments with
  | nil => rfl
  | cons segment segments ih =>
      simp only [List.flatMap_cons, UnaryFieldEncoderMachine.unaryFields_append,
        scan_append, scan_segment]
      rw [ih]

/-- Select either the four coordinate fields or the single route-index field from each record. -/
def compiler {InputSymbol : Type} [Fintype InputSymbol]
    (segments : List InputSymbol → List IndexedGridSegment) (coordinates : Bool)
    (source : TM2ComputableInPolyTime id unaryFields
      (fun input => (segments input).flatMap PeriodicGridDrawing.Arithmetic.segmentFields)) :
    TM2ComputableInPolyTime id unaryFields (fun input => (segments input).flatMap (fields coordinates)) := by
  let raw := TM2PolyTimeInputEncodingTransport.of_prepare unaryFields
    (FiniteStateTransducer.computableInPolyTime (0 : Fin 6) (transition coordinates) (fun _ => []))
    (fun _ => rfl) (fun _ => rfl)
  let physical := TM2CompositionMachine.computableInPolyTime source raw
  apply TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq physical
  intro input
  simp only [id_eq, output, scan_segments, List.append_nil]

def countCompiler {InputSymbol : Type} [Fintype InputSymbol]
    (segments : List InputSymbol → List IndexedGridSegment)
    (source : TM2ComputableInPolyTime id unaryFields
      (fun input => (segments input).flatMap PeriodicGridDrawing.Arithmetic.segmentFields)) :
    TM2ComputableInPolyTime id unaryFields (fun input => [(segments input).length]) := by
  let physical := TM2CompositionMachine.computableInPolyTime (compiler segments false source)
    UnaryFieldAggregate.countCompiler
  apply TM2ComputableInPolyTime.of_eq physical
  intro input
  simp [fields]

end LeanTrominoes.UnarySegmentFieldsProjection
end
