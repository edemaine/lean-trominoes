/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierSpanRouteDirectionDecoder

/-! # Semantics of retained carrier-span route decoding -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierSpanRouteDirections

open FiniteStateTransducer
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

private theorem first_scan_many (horizontal : Bool) : ∀ count : Nat,
    scan (firstTransition horizontal) .many
        (List.replicate count UnaryFieldEncoderMachine.Symbol.unit ++
          [UnaryFieldEncoderMachine.Symbol.delimiter]) =
      (.many,
        List.replicate count (.direction (dynamicDirection horizontal)) ++
          firstSuffix horizontal)
  | 0 => by
      simp [scan, firstTransition]
  | count + 1 => by
      rw [List.replicate_succ, List.cons_append]
      simp only [scan, firstTransition, List.singleton_append]
      rw [first_scan_many horizontal count]
      simp [List.replicate_succ]

private theorem last_scan_many (horizontal : Bool) : ∀ count : Nat,
    scan (lastTransition horizontal) .many
        (List.replicate count UnaryFieldEncoderMachine.Symbol.unit ++
          [UnaryFieldEncoderMachine.Symbol.delimiter]) =
      (.many,
        List.replicate count (.direction (dynamicDirection horizontal)) ++
          [.routeEnd])
  | 0 => by
      simp [scan, lastTransition]
  | count + 1 => by
      rw [List.replicate_succ, List.cons_append]
      simp only [scan, lastTransition, List.singleton_append]
      rw [last_scan_many horizontal count]
      simp [List.replicate_succ]

private theorem first_scan_nine (horizontal : Bool) :
    scan (firstTransition horizontal) .zero
        (List.replicate 9 UnaryFieldEncoderMachine.Symbol.unit) =
      (.many,
        firstPrefix horizontal ++
          List.replicate 4
            (.direction (dynamicDirection horizontal))) := by
  cases horizontal <;> rfl

private theorem last_scan_nine (horizontal : Bool) :
    scan (lastTransition horizontal) .zero
        (List.replicate 9 UnaryFieldEncoderMachine.Symbol.unit) =
      (.many,
        [.direction (dynamicDirection horizontal)]) := by
  cases horizontal <;> rfl

@[simp] theorem firstOutput_unaryField_zero (horizontal : Bool) :
    firstOutput horizontal (UnaryFieldEncoderMachine.unaryField 0) = [] := by
  cases horizontal <;> rfl

@[simp] theorem lastOutput_unaryField_zero (horizontal : Bool) :
    lastOutput horizontal (UnaryFieldEncoderMachine.unaryField 0) = [] := by
  cases horizontal <;> rfl

theorem firstOutput_unaryField_span (horizontal : Bool) (span : Nat)
    (large : 6 < span) :
    firstOutput horizontal
        (UnaryFieldEncoderMachine.unaryField (span + 2)) =
      firstPrefix horizontal ++
        List.replicate (span - 3)
          (.direction (dynamicDirection horizontal)) ++
        firstSuffix horizontal := by
  obtain ⟨extra, rfl⟩ : ∃ extra, span = 7 + extra := by
    exact Nat.exists_eq_add_of_le (by omega)
  unfold firstOutput FiniteStateTransducer.output
    UnaryFieldEncoderMachine.unaryField
  rw [show 7 + extra + 2 = 9 + extra by omega,
    List.replicate_add, List.append_assoc,
    FiniteStateTransducer.scan_append, first_scan_nine]
  dsimp
  rw [first_scan_many]
  simp only [finish, List.append_nil]
  simp [show 7 + extra - 3 = 4 + extra by omega,
    List.replicate_add, List.append_assoc]

theorem lastOutput_unaryField_span (horizontal : Bool) (span : Nat)
    (large : 6 < span) :
    lastOutput horizontal
        (UnaryFieldEncoderMachine.unaryField (span + 2)) =
      List.replicate (span - 6)
          (.direction (dynamicDirection horizontal)) ++
        [.routeEnd] := by
  obtain ⟨extra, rfl⟩ : ∃ extra, span = 7 + extra := by
    exact Nat.exists_eq_add_of_le (by omega)
  unfold lastOutput FiniteStateTransducer.output
    UnaryFieldEncoderMachine.unaryField
  rw [show 7 + extra + 2 = 9 + extra by omega,
    List.replicate_add, List.append_assoc,
    FiniteStateTransducer.scan_append, last_scan_nine]
  dsimp
  rw [last_scan_many]
  simp only [finish, List.append_nil]
  simp [show 7 + extra - 6 = 1 + extra by omega,
    List.replicate_add]

theorem blockOutput_unaryField_span (horizontal : Bool) (span : Nat)
    (large : 6 < span) :
    blockOutput horizontal
        (UnaryFieldEncoderMachine.unaryField (span + 2)) =
      canonicalBlock horizontal span := by
  have spanThree : ((span : Int) - 3).natAbs = span - 3 := by
    exact Int.ofNat_inj.mp
      ((Int.natAbs_of_nonneg (by omega)).trans (by omega))
  have spanSix : ((span : Int) - 6).natAbs = span - 6 := by
    exact Int.ofNat_inj.mp
      ((Int.natAbs_of_nonneg (by omega)).trans (by omega))
  rw [blockOutput, firstOutput_unaryField_span horizontal span large,
    lastOutput_unaryField_span horizontal span large]
  cases horizontal <;>
    simp [canonicalBlock, delimitedDirections, directionTokens,
      carrierLensRouteDirections, firstPrefix, firstSuffix,
      dynamicDirection, spanThree, spanSix, List.map_append,
      List.map_replicate, List.append_assoc]

@[simp] theorem blockOutput_unaryField_zero (horizontal : Bool) :
    blockOutput horizontal (UnaryFieldEncoderMachine.unaryField 0) = [] := by
  simp [blockOutput]

end CarrierSpanRouteDirections
end LeanTrominoes.PeriodicOrthocrossing
