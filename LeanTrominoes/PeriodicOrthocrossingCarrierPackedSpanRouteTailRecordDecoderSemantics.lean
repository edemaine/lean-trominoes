/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BinaryRouteTailRecordFormatterSemantics
import LeanTrominoes.BooleanListUnaryFieldCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierPackedSpanRouteTailRecordDecoder
import LeanTrominoes.PeriodicOrthocrossingCarrierSpanRouteDirectionDecoderSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierTaggedSpanRouteDirectionDecoderSemantics

/-! # Semantics of packed retained carrier Figure 9 tail-record decoding -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierPackedSpanRouteTailRecords

open FiniteStateTransducer
open CarrierSpanRouteDirections
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

private theorem reduced_scan_quads (count : Nat)
    (suffix : List SourceSymbol) :
    scan reducedTransition .four
        (List.replicate (4 * count)
          UnaryFieldEncoderMachine.Symbol.unit ++ suffix) =
      let rest := scan reducedTransition .four suffix
      (rest.1,
        List.replicate count UnaryFieldEncoderMachine.Symbol.unit ++
          rest.2) := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [show 4 * (count + 1) = 4 + 4 * count by omega,
        List.replicate_add]
      change scan reducedTransition .four
        (.unit :: .unit :: .unit :: .unit ::
          (List.replicate (4 * count)
            UnaryFieldEncoderMachine.Symbol.unit ++ suffix)) = _
      simp only [scan, reducedTransition, List.nil_append,
        List.singleton_append]
      rw [induction]
      simp [List.replicate_succ]

private theorem replicate_append_unit (count : Nat) :
    List.replicate count UnaryFieldEncoderMachine.Symbol.unit ++
        [UnaryFieldEncoderMachine.Symbol.unit] =
      UnaryFieldEncoderMachine.Symbol.unit ::
        List.replicate count UnaryFieldEncoderMachine.Symbol.unit := by
  rw [← List.replicate_succ', List.replicate_succ]

private theorem unit_cons_replicate_append_unit (count : Nat) :
    UnaryFieldEncoderMachine.Symbol.unit ::
        (List.replicate count UnaryFieldEncoderMachine.Symbol.unit ++
          [UnaryFieldEncoderMachine.Symbol.unit,
            UnaryFieldEncoderMachine.Symbol.delimiter]) =
      List.replicate (count + 2) UnaryFieldEncoderMachine.Symbol.unit ++
        [UnaryFieldEncoderMachine.Symbol.delimiter] := by
  change
    (UnaryFieldEncoderMachine.Symbol.unit ::
      List.replicate count UnaryFieldEncoderMachine.Symbol.unit) ++
        [UnaryFieldEncoderMachine.Symbol.unit,
          UnaryFieldEncoderMachine.Symbol.delimiter] = _
  rw [← List.replicate_succ]
  rw [show
      [UnaryFieldEncoderMachine.Symbol.unit,
        UnaryFieldEncoderMachine.Symbol.delimiter] =
      List.replicate 1 UnaryFieldEncoderMachine.Symbol.unit ++
        [UnaryFieldEncoderMachine.Symbol.delimiter] by rfl,
    ← List.append_assoc, ← List.replicate_add]

@[simp] theorem reducedOutput_unaryField_zero :
    reducedOutput (UnaryFieldEncoderMachine.unaryField 0) =
      UnaryFieldEncoderMachine.unaryField 0 := by
  rfl

/-- Every positive packed residue has the same span-decoder quotient. -/
theorem reducedOutput_unaryField_packed
    (span : Nat) (residue : Residue) :
    reducedOutput
        (UnaryFieldEncoderMachine.unaryField
          (4 * span + 4 + residue.code)) =
      UnaryFieldEncoderMachine.unaryField (span + 2) := by
  unfold reducedOutput FiniteStateTransducer.output
    UnaryFieldEncoderMachine.unaryField
  rw [show 4 * span + 4 + residue.code =
      4 + 4 * span + residue.code by omega,
    List.replicate_add, List.replicate_add]
  change
    (scan reducedTransition .zero
      (.unit :: .unit :: .unit :: .unit ::
        (List.replicate (4 * span) .unit ++
          List.replicate residue.code .unit ++ [.delimiter]))).2 ++
      reducedFinish
        (scan reducedTransition .zero
          (.unit :: .unit :: .unit :: .unit ::
            (List.replicate (4 * span) .unit ++
              List.replicate residue.code .unit ++ [.delimiter]))).1 = _
  simp only [scan, reducedTransition, List.nil_append,
    List.singleton_append]
  rw [show
      List.replicate (4 * span) UnaryFieldEncoderMachine.Symbol.unit ++
          List.replicate residue.code UnaryFieldEncoderMachine.Symbol.unit ++
            [UnaryFieldEncoderMachine.Symbol.delimiter] =
        List.replicate (4 * span) UnaryFieldEncoderMachine.Symbol.unit ++
          (List.replicate residue.code UnaryFieldEncoderMachine.Symbol.unit ++
            [UnaryFieldEncoderMachine.Symbol.delimiter]) by
      rw [List.append_assoc],
    reduced_scan_quads]
  cases residue <;>
    simp only [Residue.code, List.replicate_zero, List.nil_append,
      List.replicate_succ, scan, reducedTransition, reducedFinish,
      List.append_nil]
  all_goals
    exact unit_cons_replicate_append_unit span

private theorem residue_scan_quads (target : Residue)
    (value : Residue) (count : Nat) (suffix : List SourceSymbol) :
    scan (residueTransition target) (.residue value)
        (List.replicate (4 * count)
          UnaryFieldEncoderMachine.Symbol.unit ++ suffix) =
      scan (residueTransition target) (.residue value) suffix := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [show 4 * (count + 1) = 4 + 4 * count by omega,
        List.replicate_add]
      change scan (residueTransition target) (.residue value)
        (.unit :: .unit :: .unit :: .unit ::
          (List.replicate (4 * count) .unit ++ suffix)) = _
      cases value <;>
        simp only [scan, residueTransition, Residue.next,
          List.nil_append] <;>
        exact induction

theorem residueOutput_unaryField_packed
    (target residue : Residue) (span : Nat) :
    residueOutput target
        (UnaryFieldEncoderMachine.unaryField
          (4 * span + 4 + residue.code)) =
      [residue == target] := by
  unfold residueOutput FiniteStateTransducer.output
    UnaryFieldEncoderMachine.unaryField
  rw [show 4 * span + 4 + residue.code =
      4 * (span + 1) + residue.code by omega,
    List.replicate_add, List.append_assoc,
    residue_scan_quads]
  cases target <;> cases residue <;>
    rfl

theorem hasResidue_unaryField_packed
    (target residue : Residue) (span : Nat) :
    hasResidue target
        (UnaryFieldEncoderMachine.unaryField
          (4 * span + 4 + residue.code)) =
      (residue == target) := by
  unfold hasResidue
  rw [residueOutput_unaryField_packed]
  rfl

@[simp] theorem hasResidue_unaryField_zero (target : Residue) :
    hasResidue target (UnaryFieldEncoderMachine.unaryField 0) =
      (.zero == target) := by
  cases target <;> rfl

theorem candidate_unaryField_packed
    (horizontal nextSlice : Bool) (span : Nat) (large : 6 < span)
    (residue : Residue) :
    candidate horizontal nextSlice
        (UnaryFieldEncoderMachine.unaryField
          (4 * span + 4 + residue.code)) =
      carrierLensRouteTailRecordBlock horizontal nextSlice span := by
  unfold candidate
  rw [reducedOutput_unaryField_packed,
    CarrierSpanRouteDirections.blockOutput_unaryField_span
      horizontal span large,
    BinaryRouteTailRecordFormatter.output_carrier_canonicalBlock]

@[simp] theorem candidate_unaryField_zero
    (horizontal nextSlice : Bool) :
    candidate horizontal nextSlice
        (UnaryFieldEncoderMachine.unaryField 0) = [] := by
  unfold candidate
  rw [reducedOutput_unaryField_zero,
    CarrierSpanRouteDirections.blockOutput_unaryField_zero]
  rfl

@[simp] theorem blockOutput_unaryField_zero :
    blockOutput (UnaryFieldEncoderMachine.unaryField 0) = [] := by
  simp [blockOutput, guardedCandidate,
    SeparatedBooleanGuard.guarded]

/-- The residue selects exactly the carrier axis and next-slice profile while
the quotient supplies the unbounded span. -/
theorem blockOutput_unaryField_packed
    (horizontal nextSlice : Bool) (span : Nat) (large : 6 < span) :
    blockOutput
        (UnaryFieldEncoderMachine.unaryField
          (4 * span + 4 +
            2 * BooleanListUnaryFields.bitNat horizontal +
              BooleanListUnaryFields.bitNat nextSlice)) =
      carrierLensRouteTailRecordBlock horizontal nextSlice span := by
  have codeEq :
      2 * BooleanListUnaryFields.bitNat horizontal +
          BooleanListUnaryFields.bitNat nextSlice =
        (metadataResidue horizontal nextSlice).code := by
    cases horizontal <;> cases nextSlice <;> rfl
  rw [show
      4 * span + 4 +
          2 * BooleanListUnaryFields.bitNat horizontal +
            BooleanListUnaryFields.bitNat nextSlice =
        4 * span + 4 +
          (2 * BooleanListUnaryFields.bitNat horizontal +
            BooleanListUnaryFields.bitNat nextSlice) by omega,
    codeEq]
  have has (target : Residue) :
      hasResidue target
          (UnaryFieldEncoderMachine.unaryField
            (4 * span + 4 +
              (metadataResidue horizontal nextSlice).code)) =
        (metadataResidue horizontal nextSlice == target) :=
    hasResidue_unaryField_packed target
      (metadataResidue horizontal nextSlice) span
  have cand (candidateHorizontal candidateNextSlice : Bool) :
      candidate candidateHorizontal candidateNextSlice
          (UnaryFieldEncoderMachine.unaryField
            (4 * span + 4 +
              (metadataResidue horizontal nextSlice).code)) =
        carrierLensRouteTailRecordBlock
          candidateHorizontal candidateNextSlice span :=
    candidate_unaryField_packed
      candidateHorizontal candidateNextSlice span large
      (metadataResidue horizontal nextSlice)
  unfold blockOutput guardedCandidate
  rw [has .zero, cand false false,
    has .one, cand false true,
    has .two, cand true false,
    has .three, cand true true]
  cases horizontal <;> cases nextSlice <;>
    simp [metadataResidue, SeparatedBooleanGuard.guarded]

/-- The outer block mapper applies the packed decoder independently to every
unary matrix field. -/
theorem stream_unaryFields (values : List Nat) :
    stream (UnaryFieldEncoderMachine.unaryFields values) =
      values.flatMap fun value =>
        blockOutput (UnaryFieldEncoderMachine.unaryField value) := by
  unfold stream TM2EndDelimitedBlockMap.mappedOutput
  rw [CarrierTaggedSpanRouteDirections.blocks_unaryFields,
    List.flatMap_map]

end CarrierPackedSpanRouteTailRecords
end LeanTrominoes.PeriodicOrthocrossing
