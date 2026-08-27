/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierSpanRouteDirectionDecoderSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierTaggedSpanRouteDirectionDecoder

/-! # Semantics of parity-tagged retained carrier-span decoding -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierTaggedSpanRouteDirections

open CarrierSpanRouteDirections FiniteStateTransducer

private theorem replicate_append_unit (count : Nat) :
    List.replicate count UnaryFieldEncoderMachine.Symbol.unit ++
        [UnaryFieldEncoderMachine.Symbol.unit] =
      UnaryFieldEncoderMachine.Symbol.unit ::
        List.replicate count UnaryFieldEncoderMachine.Symbol.unit := by
  rw [← List.replicate_succ', List.replicate_succ]

private theorem reduced_scan_pairs (count : Nat)
    (suffix : List SourceSymbol) :
    scan reducedTransition .even
        (List.replicate (2 * count)
          UnaryFieldEncoderMachine.Symbol.unit ++ suffix) =
      let rest := scan reducedTransition .even suffix
      (rest.1,
        List.replicate count UnaryFieldEncoderMachine.Symbol.unit ++
          rest.2) := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [show 2 * (count + 1) = 2 + 2 * count by omega,
        List.replicate_add]
      change scan reducedTransition .even
        (UnaryFieldEncoderMachine.Symbol.unit ::
          UnaryFieldEncoderMachine.Symbol.unit ::
            (List.replicate (2 * count)
              UnaryFieldEncoderMachine.Symbol.unit ++ suffix)) = _
      simp only [scan, reducedTransition, List.nil_append,
        List.singleton_append]
      rw [induction]
      simp [List.replicate_succ]

@[simp] theorem reducedOutput_unaryField_zero :
    reducedOutput (UnaryFieldEncoderMachine.unaryField 0) =
      UnaryFieldEncoderMachine.unaryField 0 := by
  rfl

theorem reducedOutput_unaryField_even (span : Nat) :
    reducedOutput
        (UnaryFieldEncoderMachine.unaryField (2 * span + 2)) =
      UnaryFieldEncoderMachine.unaryField (span + 2) := by
  unfold reducedOutput FiniteStateTransducer.output
    UnaryFieldEncoderMachine.unaryField
  rw [show 2 * span + 2 = 2 + 2 * span by omega,
    List.replicate_add]
  change
    (scan reducedTransition .zero
      (UnaryFieldEncoderMachine.Symbol.unit ::
        UnaryFieldEncoderMachine.Symbol.unit ::
          (List.replicate (2 * span)
            UnaryFieldEncoderMachine.Symbol.unit ++
              [UnaryFieldEncoderMachine.Symbol.delimiter]))).2 ++
        reducedFinish
          (scan reducedTransition .zero
            (UnaryFieldEncoderMachine.Symbol.unit ::
              UnaryFieldEncoderMachine.Symbol.unit ::
                (List.replicate (2 * span)
                  UnaryFieldEncoderMachine.Symbol.unit ++
                    [UnaryFieldEncoderMachine.Symbol.delimiter]))).1 = _
  simp only [scan, reducedTransition, List.nil_append,
    List.singleton_append]
  rw [reduced_scan_pairs]
  simp only [reducedFinish, scan, reducedTransition, List.append_nil]
  rw [show
      [UnaryFieldEncoderMachine.Symbol.unit,
        UnaryFieldEncoderMachine.Symbol.delimiter] =
        [UnaryFieldEncoderMachine.Symbol.unit] ++
          [UnaryFieldEncoderMachine.Symbol.delimiter] by rfl,
    ← List.append_assoc, replicate_append_unit]
  rfl

theorem reducedOutput_unaryField_odd (span : Nat) :
    reducedOutput
        (UnaryFieldEncoderMachine.unaryField (2 * span + 3)) =
      UnaryFieldEncoderMachine.unaryField (span + 2) := by
  unfold reducedOutput FiniteStateTransducer.output
    UnaryFieldEncoderMachine.unaryField
  rw [show 2 * span + 3 = 2 + 2 * span + 1 by omega,
    List.replicate_add, List.replicate_add]
  change
    (scan reducedTransition .zero
      (UnaryFieldEncoderMachine.Symbol.unit ::
        UnaryFieldEncoderMachine.Symbol.unit ::
          (List.replicate (2 * span)
            UnaryFieldEncoderMachine.Symbol.unit ++
              [UnaryFieldEncoderMachine.Symbol.unit] ++
                [UnaryFieldEncoderMachine.Symbol.delimiter]))).2 ++
        reducedFinish
          (scan reducedTransition .zero
            (UnaryFieldEncoderMachine.Symbol.unit ::
              UnaryFieldEncoderMachine.Symbol.unit ::
                (List.replicate (2 * span)
                  UnaryFieldEncoderMachine.Symbol.unit ++
                    [UnaryFieldEncoderMachine.Symbol.unit] ++
                      [UnaryFieldEncoderMachine.Symbol.delimiter]))).1 = _
  simp only [scan, reducedTransition, List.nil_append,
    List.singleton_append]
  rw [List.append_assoc]
  rw [reduced_scan_pairs]
  simp only [reducedFinish, List.singleton_append, scan,
    reducedTransition, List.append_nil]
  simp only [List.nil_append]
  rw [show
      [UnaryFieldEncoderMachine.Symbol.unit,
        UnaryFieldEncoderMachine.Symbol.delimiter] =
        [UnaryFieldEncoderMachine.Symbol.unit] ++
          [UnaryFieldEncoderMachine.Symbol.delimiter] by rfl,
    ← List.append_assoc, replicate_append_unit]
  simp [List.replicate_succ]

private theorem axis_scan_pairs (count : Nat)
    (suffix : List SourceSymbol) :
    scan axisTransition .even
        (List.replicate (2 * count)
          UnaryFieldEncoderMachine.Symbol.unit ++ suffix) =
      scan axisTransition .even suffix := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [show 2 * (count + 1) = 2 + 2 * count by omega,
        List.replicate_add]
      change scan axisTransition .even
        (UnaryFieldEncoderMachine.Symbol.unit ::
          UnaryFieldEncoderMachine.Symbol.unit ::
            (List.replicate (2 * count)
              UnaryFieldEncoderMachine.Symbol.unit ++ suffix)) = _
      simp only [scan, axisTransition, List.nil_append]
      exact induction

theorem isHorizontal_unaryField_even (span : Nat) :
    isHorizontal
        (UnaryFieldEncoderMachine.unaryField (2 * span + 2)) = false := by
  unfold isHorizontal axisOutput FiniteStateTransducer.output
    UnaryFieldEncoderMachine.unaryField
  rw [show 2 * span + 2 = 2 * (span + 1) by omega,
    axis_scan_pairs]
  rfl

theorem isHorizontal_unaryField_odd (span : Nat) :
    isHorizontal
        (UnaryFieldEncoderMachine.unaryField (2 * span + 3)) = true := by
  unfold isHorizontal axisOutput FiniteStateTransducer.output
    UnaryFieldEncoderMachine.unaryField
  rw [show 2 * span + 3 = 2 * (span + 1) + 1 by omega,
    List.replicate_add]
  dsimp
  rw [List.append_assoc, axis_scan_pairs]
  rfl

@[simp] theorem isHorizontal_unaryField_zero :
    isHorizontal (UnaryFieldEncoderMachine.unaryField 0) = false := by
  rfl

@[simp] theorem blockOutput_unaryField_zero :
    blockOutput (UnaryFieldEncoderMachine.unaryField 0) = [] := by
  simp [blockOutput, verticalCandidate,
    isHorizontal_unaryField_zero, reducedOutput_unaryField_zero,
    SeparatedBooleanGuard.guarded,
    CarrierSpanRouteDirections.blockOutput_unaryField_zero]

theorem blockOutput_unaryField_even (span : Nat) (large : 6 < span) :
    blockOutput
        (UnaryFieldEncoderMachine.unaryField (2 * span + 2)) =
      CarrierSpanRouteDirections.canonicalBlock false span := by
  simp [blockOutput, verticalCandidate,
    isHorizontal_unaryField_even, reducedOutput_unaryField_even,
    SeparatedBooleanGuard.guarded,
    CarrierSpanRouteDirections.blockOutput_unaryField_span false span large]

theorem blockOutput_unaryField_odd (span : Nat) (large : 6 < span) :
    blockOutput
        (UnaryFieldEncoderMachine.unaryField (2 * span + 3)) =
      CarrierSpanRouteDirections.canonicalBlock true span := by
  simp [blockOutput, horizontalCandidate,
    isHorizontal_unaryField_odd, reducedOutput_unaryField_odd,
    SeparatedBooleanGuard.guarded,
    CarrierSpanRouteDirections.blockOutput_unaryField_span true span large]

end CarrierTaggedSpanRouteDirections
end LeanTrominoes.PeriodicOrthocrossing
