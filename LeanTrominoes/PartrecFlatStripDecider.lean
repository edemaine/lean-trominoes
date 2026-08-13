/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PartrecAdd
import LeanTrominoes.PartrecBinaryLength
import LeanTrominoes.PartrecPowerTwo
import LeanTrominoes.PartrecFlatStripCycle
import LeanTrominoes.PartrecFlatStripWellFormed
import LeanTrominoes.PartrecFlatSavitchReachSpace

/-!
# Complete native-flat periodic-strip decider

This module computes the Savitch parameters directly from the target flat
field list, guards the cycle search by structural well-formedness, and exposes
one evaluator for periodic-strip tromino tiling.
-/

namespace LeanTrominoes
namespace PeriodicStrip
namespace RawWindowState
namespace FlatStripDeciderPartrec

open LeanTrominoes.Computability
open LeanTrominoes.FiniteState
open Turing ToPartrec
open Turing.PartrecToTM2

attribute [local simp] Part.bind_eq_bind

private theorem comp_eval_pure
    (outer inner : Code) (input output : List Nat)
    (innerCorrect : inner.eval input = pure output) :
    (outer.comp inner).eval input = outer.eval output := by
  simp [innerCorrect, Part.bind_eq_bind]

/-- Binary payload length without the final flat-list delimiter. -/
def fieldPayloadSpace (fields : List Nat) : Nat :=
  (fields.map fun field => (Computability.encodeNat field).length + 1).sum

theorem encodedListSpace_eq_fieldPayloadSpace (fields : List Nat) :
    encodedListSpace fields = fieldPayloadSpace fields := by
  induction fields with
  | nil => simp [fieldPayloadSpace, encodedListSpace_nil]
  | cons field fields induction =>
      simp [fieldPayloadSpace, encodedListSpace_cons, induction]

/-- One streaming input-length update on `[accumulator, field] ++ rest`. -/
def encodedListSpaceStepCode : Code :=
  let fieldLength := Code.binaryEncodingLengthCode.comp (Code.get 1)
  let increment := (Code.addConst 1).comp fieldLength
  Code.prepend
    (Code.natAddCode.comp (Code.prepend (Code.get 0) increment))
    (Code.drop 2)

def encodedListSpaceStep (values : List Nat) : List Nat :=
  (values[0]?.getD 0 +
    (Computability.encodeNat (values[1]?.getD 0)).length + 1) ::
      values.drop 2

@[simp]
theorem encodedListSpaceStepCode_eval (values : List Nat) :
    encodedListSpaceStepCode.eval values =
      pure (encodedListSpaceStep values) := by
  simp [encodedListSpaceStepCode, encodedListSpaceStep,
    LeanTrominoes.Computability.binaryEncodingLength_eq]
  omega

theorem encodedListSpaceStep_iterate
    (fields : List Nat) (accumulator : Nat) :
    (encodedListSpaceStep^[fields.length]) (accumulator :: fields) =
      [accumulator + fieldPayloadSpace fields] := by
  induction fields generalizing accumulator with
  | nil => simp [fieldPayloadSpace]
  | cons field fields induction =>
      rw [List.length_cons, Function.iterate_succ_apply]
      change (encodedListSpaceStep^[fields.length])
        ((accumulator + (Computability.encodeNat field).length + 1) ::
          fields) = _
      rw [induction]
      simp [fieldPayloadSpace]
      omega

/-- The number of natural fields in a canonical flat strip presentation. -/
def flatStripFieldCountCode : Code :=
  (Code.addConst 3).comp <|
    Code.natAddCode.comp <|
      Code.prepend (Code.get 2) (Code.get 2)

@[simp]
theorem flatStripFieldCountCode_eval (periodicStrip : PeriodicStrip) :
    flatStripFieldCountCode.eval
        (PeriodicStripFlatEncoding.stripFields periodicStrip) =
      pure [(PeriodicStripFlatEncoding.stripFields periodicStrip).length] := by
  have third :
      (PeriodicStripFlatEncoding.stripFields periodicStrip)[2]?.getD 0 =
        periodicStrip.motif.length := by
    simp [PeriodicStripFlatEncoding.stripFields]
  simp [flatStripFieldCountCode, third,
    PeriodicStripFlatEncoding.stripFields_length]
  omega

/-- Prepare the exact streaming fold as `[field count, 0] ++ fields`. -/
def flatStripEncodedListSpaceInputCode : Code :=
  Code.prepend flatStripFieldCountCode <|
    Code.prepend Code.zero Code.id

@[simp]
theorem flatStripEncodedListSpaceInputCode_eval
    (periodicStrip : PeriodicStrip) :
    flatStripEncodedListSpaceInputCode.eval
        (PeriodicStripFlatEncoding.stripFields periodicStrip) =
      pure ((PeriodicStripFlatEncoding.stripFields periodicStrip).length ::
        0 :: PeriodicStripFlatEncoding.stripFields periodicStrip) := by
  simp [flatStripEncodedListSpaceInputCode]

/-- Compute the target flat encoding length from its native field list. -/
def flatStripEncodedListSpaceCode : Code :=
  (Code.flatIterate encodedListSpaceStepCode).comp
    flatStripEncodedListSpaceInputCode

@[simp]
theorem flatStripEncodedListSpaceCode_eval
    (periodicStrip : PeriodicStrip) :
    flatStripEncodedListSpaceCode.eval
        (PeriodicStripFlatEncoding.stripFields periodicStrip) =
      pure [(PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length] := by
  let fields := PeriodicStripFlatEncoding.stripFields periodicStrip
  have inputRun := flatStripEncodedListSpaceInputCode_eval periodicStrip
  calc
    _ = (Code.flatIterate encodedListSpaceStepCode).eval
        (fields.length :: 0 :: fields) := by
      simpa [flatStripEncodedListSpaceCode, fields] using
        comp_eval_pure _ _ _ _ inputRun
    _ = pure ((encodedListSpaceStep^[fields.length]) (0 :: fields)) :=
      Code.flatIterate_eval encodedListSpaceStepCode encodedListSpaceStep
        encodedListSpaceStepCode_eval fields.length (0 :: fields)
    _ = pure [0 + fieldPayloadSpace fields] := by
      rw [encodedListSpaceStep_iterate]
    _ = _ := by
      rw [Nat.zero_add, ← encodedListSpace_eq_fieldPayloadSpace]
      simpa [fields, PeriodicStripFlatEncoding.finEncoding_encode_length,
        encodedListSpace_eq_sum]

/-- Prepare `[flat input length, 1]` for the affine depth loop. -/
def flatStripSearchDepthInputCode : Code :=
  Code.prepend flatStripEncodedListSpaceCode Code.one

@[simp]
theorem flatStripSearchDepthInputCode_eval
    (periodicStrip : PeriodicStrip) :
    flatStripSearchDepthInputCode.eval
        (PeriodicStripFlatEncoding.stripFields periodicStrip) =
      pure [(PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length,
        1] := by
  simp [flatStripSearchDepthInputCode]

/-- Compute the certified Savitch depth from native flat fields. -/
def flatStripSearchDepthCode : Code :=
  (Code.flatIterate (Code.addConst 21)).comp
    flatStripSearchDepthInputCode

@[simp]
theorem flatStripSearchDepthCode_eval (periodicStrip : PeriodicStrip) :
    flatStripSearchDepthCode.eval
        (PeriodicStripFlatEncoding.stripFields periodicStrip) =
      pure [flatStripSearchDepth periodicStrip] := by
  let inputLength :=
    (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length
  calc
    _ = (Code.flatIterate (Code.addConst 21)).eval [inputLength, 1] := by
      simpa [flatStripSearchDepthCode, inputLength] using
        comp_eval_pure _ _ _ _
          (flatStripSearchDepthInputCode_eval periodicStrip)
    _ = pure (((Code.addConstListStep 21)^[inputLength]) [1]) :=
      Code.flatIterate_eval (Code.addConst 21)
        (Code.addConstListStep 21)
        (Code.addConstListStepCode_eval 21) inputLength [1]
    _ = pure [1 + inputLength * 21] := by
      rw [Code.addConstListStep_iterate]
    _ = _ := by
      simp [flatStripSearchDepth, inputLength]
      omega

/-- Compute the padded power-of-two graph size from native flat fields. -/
def flatStripStateBoundCode : Code :=
  Code.powerTwoCode.comp flatStripSearchDepthCode

@[simp]
theorem flatStripStateBoundCode_eval (periodicStrip : PeriodicStrip) :
    flatStripStateBoundCode.eval
        (PeriodicStripFlatEncoding.stripFields periodicStrip) =
      pure [flatStripStateBound periodicStrip] := by
  simp [flatStripStateBoundCode, flatStripStateBound]

/-- Prepend the computed graph size and search depth to the untouched flat
strip fields consumed by the parameterized cycle search. -/
def flatStripCycleParametersCode : Code :=
  Code.prepend flatStripStateBoundCode <|
    Code.prepend flatStripSearchDepthCode Code.id

@[simp]
theorem flatStripCycleParametersCode_eval (periodicStrip : PeriodicStrip) :
    flatStripCycleParametersCode.eval
        (PeriodicStripFlatEncoding.stripFields periodicStrip) =
      pure ([flatStripStateBound periodicStrip,
        flatStripSearchDepth periodicStrip] ++
          PeriodicStripFlatEncoding.stripFields periodicStrip) := by
  simp [flatStripCycleParametersCode]

/-- Boolean decided by the complete native-flat evaluator. -/
def flatPeriodicStripTrominoTilingBool
    (tromino : Tromino) (periodicStrip : PeriodicStrip) : Bool :=
  if wellFormed : periodicStrip.IsWellFormed then
    cycleSearchIndexDFSBoolAtDepth
      (flatStripStateBound periodicStrip)
      (flatStripSearchDepth periodicStrip)
      (indexedTransitionBool tromino periodicStrip wellFormed.2.1)
  else
    false

theorem flatPeriodicStripTrominoTilingBool_eq_true_iff
    (tromino : Tromino) (periodicStrip : PeriodicStrip) :
    flatPeriodicStripTrominoTilingBool tromino periodicStrip = true ↔
      PeriodicStripTrominoTiling tromino periodicStrip := by
  by_cases wellFormed : periodicStrip.IsWellFormed
  · rw [flatPeriodicStripTrominoTilingBool, dif_pos wellFormed,
      cycleSearchIndexDFSBoolAtDepth_eq,
      cycleSearchIndexBoolAtDepth_eq_true_iff
        (flatStripStateBound periodicStrip)
        (flatStripSearchDepth periodicStrip)
        (indexedTransitionBool tromino periodicStrip wellFormed.2.1)
        (by simp [flatStripStateBound]),
      paddedIndexed_hasCycle_iff_hasCycle tromino periodicStrip
        wellFormed.2.1 (flatStripStateBound periodicStrip)
        (indexCount_le_flatStripStateBound periodicStrip),
      ← WindowState.tileable_iff_hasCycle tromino wellFormed]
    simp [PeriodicStripTrominoTiling, wellFormed]
  · rw [flatPeriodicStripTrominoTilingBool, dif_neg wellFormed]
    simp [PeriodicStripTrominoTiling, wellFormed]

/-- Reject malformed strip structures before running the complete cycle
search. -/
def flatPeriodicStripTrominoTilingCode (tromino : Tromino) : Code :=
  Code.branchZero Code.flatStripWellFormedCode Code.zero <|
    (FlatStripCyclePartrec.flatStripCycleSearchCode tromino).comp
      flatStripCycleParametersCode

private theorem encodeBool_eq_divideBoolTag (value : Bool) :
    Encodable.encode value = divideBoolTag value := by
  cases value <;> rfl

@[simp]
theorem flatPeriodicStripTrominoTilingCode_eval
    (tromino : Tromino) (periodicStrip : PeriodicStrip) :
    (flatPeriodicStripTrominoTilingCode tromino).eval
        (PeriodicStripFlatEncoding.stripFields periodicStrip) =
      pure [Encodable.encode
        (flatPeriodicStripTrominoTilingBool tromino periodicStrip)] := by
  let fields := PeriodicStripFlatEncoding.stripFields periodicStrip
  by_cases wellFormed : periodicStrip.IsWellFormed
  · have wellFormedBool : periodicStrip.wellFormed = true :=
      (periodicStrip.wellFormed_eq_true_iff).mpr wellFormed
    let result := cycleSearchIndexDFSBoolAtDepth
      (flatStripStateBound periodicStrip)
      (flatStripSearchDepth periodicStrip)
      (indexedTransitionRawBool tromino periodicStrip)
    have parameterRun := flatStripCycleParametersCode_eval periodicStrip
    have cycleRun :
        ((FlatStripCyclePartrec.flatStripCycleSearchCode tromino).comp
          flatStripCycleParametersCode).eval fields =
          pure [divideBoolTag result] := by
      calc
        _ = (FlatStripCyclePartrec.flatStripCycleSearchCode tromino).eval
            ([flatStripStateBound periodicStrip,
              flatStripSearchDepth periodicStrip] ++ fields) := by
          simpa [fields] using comp_eval_pure _ _ _ _ parameterRun
        _ = _ := by
          simpa [fields, result] using
            FlatStripCyclePartrec.flatStripCycleSearchCode_eval
              tromino periodicStrip wellFormed
              (flatStripStateBound periodicStrip)
              (flatStripSearchDepth periodicStrip)
    have guardedRun := Code.branchZero_eval_succ_at
      Code.flatStripWellFormedCode Code.zero
      ((FlatStripCyclePartrec.flatStripCycleSearchCode tromino).comp
        flatStripCycleParametersCode)
      fields 1
      (by simpa [fields, wellFormedBool] using
        Code.flatStripWellFormedCode_eval periodicStrip)
      [divideBoolTag result] cycleRun (by omega)
    have resultEq :
        cycleSearchIndexDFSBoolAtDepth
            (flatStripStateBound periodicStrip)
            (flatStripSearchDepth periodicStrip)
            (indexedTransitionBool tromino periodicStrip wellFormed.2.1) =
          result := by
      rfl
    rw [flatPeriodicStripTrominoTilingCode,
      flatPeriodicStripTrominoTilingBool, dif_pos wellFormed,
      encodeBool_eq_divideBoolTag, resultEq]
    simpa [fields, result] using guardedRun
  · have wellFormedBool : periodicStrip.wellFormed = false := by
      apply Bool.eq_false_iff.mpr
      intro true
      exact wellFormed ((periodicStrip.wellFormed_eq_true_iff).mp true)
    have guardedRun := Code.branchZero_eval_zero_at
      Code.flatStripWellFormedCode Code.zero
      ((FlatStripCyclePartrec.flatStripCycleSearchCode tromino).comp
        flatStripCycleParametersCode)
      fields 0
      (by simpa [fields, wellFormedBool] using
        Code.flatStripWellFormedCode_eval periodicStrip)
      [0] (by simp) rfl
    rw [flatPeriodicStripTrominoTilingCode,
      flatPeriodicStripTrominoTilingBool, dif_neg wellFormed,
      encodeBool_eq_divideBoolTag]
    simpa [fields, divideBoolTag] using guardedRun

end FlatStripDeciderPartrec
end RawWindowState
end PeriodicStrip
end LeanTrominoes
