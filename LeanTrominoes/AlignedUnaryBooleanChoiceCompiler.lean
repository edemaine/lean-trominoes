/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.AlignedUnaryListClosure
import LeanTrominoes.BooleanListUnaryFieldCompiler
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.UnaryFieldAlternatingPaddingCompiler
import LeanTrominoes.UnaryFieldConstantScaleCompiler
import LeanTrominoes.UnaryFieldRangeCompiler
import LeanTrominoes.UnaryIndexedValueLookupCompiler
import LeanTrominoes.UnaryIndexedValueLookupSemantics

/-! # Boolean choice between aligned unary columns -/

noncomputable section

namespace LeanTrominoes.AlignedUnaryBooleanChoice

open Computability Turing

/-- Consecutive even query bases `0, 2, ..., 2(n - 1)`. -/
def doubledPositions (first : List Nat) : List Nat :=
  UnaryFieldConstantScale.values 2 (UnaryFieldRange.values first)

/-- A false control queries the first column and a true control queries the
second column. -/
def queries (controls : List Bool) (first : List Nat) : List Nat :=
  AlignedUnaryListClosure.added
    (doubledPositions first) (BooleanListUnaryFields.values controls)

/-- Interleave aligned columns as `[first₀, second₀, first₁, second₁,
…]`. -/
def candidateValues (first second : List Nat) : List Nat :=
  AlignedUnaryListClosure.added
    (UnaryFieldAlternatingPadding.appendZeroValues first)
    (UnaryFieldAlternatingPadding.prependZeroValues second)

/-- Select one value per aligned Boolean control. -/
def selectedValues (controls : List Bool)
    (first second : List Nat) : List Nat :=
  UnaryIndexedValueLookup.values
    (queries controls first) (candidateValues first second)

@[simp] theorem doubledPositions_length (first : List Nat) :
    (doubledPositions first).length = first.length := by
  simp [doubledPositions, UnaryFieldConstantScale.values,
    UnaryFieldRange.values]

@[simp] theorem queries_length (controls : List Bool) (first : List Nat)
    (lengthEq : controls.length = first.length) :
    (queries controls first).length = controls.length := by
  rw [queries, AlignedUnaryListClosure.added_length,
    doubledPositions_length]
  simp [BooleanListUnaryFields.values, lengthEq]

@[simp] theorem candidateValues_length (first second : List Nat)
    (lengthEq : first.length = second.length) :
    (candidateValues first second).length = 2 * first.length := by
  rw [candidateValues, AlignedUnaryListClosure.added_length,
    UnaryFieldAlternatingPadding.appendZeroValues_length,
    UnaryFieldAlternatingPadding.prependZeroValues_length, lengthEq,
    min_self]

@[simp] theorem selectedValues_length (controls : List Bool)
    (first second : List Nat)
    (controlsFirst : controls.length = first.length) :
    (selectedValues controls first second).length = controls.length := by
  rw [selectedValues, UnaryIndexedValueLookup.values_length,
    queries_length controls first controlsFirst]

/-- Equal-length Boolean and unary columns produced from one input can be
selected pointwise in polynomial time. -/
noncomputable def selectedValuesComputableInPolyTime
    {Input InputSymbol : Type}
    [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeInput : Input → List InputSymbol)
    (controls : Input → List Bool)
    (first second : Input → List Nat)
    (controlsFirst : ∀ input,
      (controls input).length = (first input).length)
    (firstSecond : ∀ input,
      (first input).length = (second input).length)
    (controlCompiler :
      @TM2ComputableInPolyTime
        Input (List Bool) InputSymbol Bool encodeInput id controls)
    (firstCompiler :
      @TM2ComputableInPolyTime
        Input (List Nat) InputSymbol UnaryFieldEncoderMachine.Symbol
        encodeInput UnaryFieldEncoderMachine.unaryFields first)
    (secondCompiler :
      @TM2ComputableInPolyTime
        Input (List Nat) InputSymbol UnaryFieldEncoderMachine.Symbol
        encodeInput UnaryFieldEncoderMachine.unaryFields second) :
    @TM2ComputableInPolyTime
      Input (List Nat) InputSymbol UnaryFieldEncoderMachine.Symbol
      encodeInput UnaryFieldEncoderMachine.unaryFields
      (fun input => selectedValues
        (controls input) (first input) (second input)) := by
  let controlValuesCompiler :=
    TM2CompositionMachine.computableInPolyTime controlCompiler
      BooleanListUnaryFields.valuesComputableInPolyTime
  let positionCompiler := TM2CompositionMachine.computableInPolyTime
    (TM2CompositionMachine.computableInPolyTime
      firstCompiler UnaryFieldRange.computableInPolyTime)
    (UnaryFieldConstantScale.computableInPolyTime 2)
  let queryCompiler := AlignedUnaryListClosure.addedComputableInPolyTime
    encodeInput
    (fun input => doubledPositions (first input))
    (fun input => BooleanListUnaryFields.values (controls input))
    (fun input => by
      simp [BooleanListUnaryFields.values, controlsFirst input])
    positionCompiler controlValuesCompiler
  let paddedFirstCompiler := TM2CompositionMachine.computableInPolyTime
    firstCompiler
      UnaryFieldAlternatingPadding.appendZeroValuesComputableInPolyTime
  let paddedSecondCompiler := TM2CompositionMachine.computableInPolyTime
    secondCompiler
      UnaryFieldAlternatingPadding.prependZeroValuesComputableInPolyTime
  let candidateCompiler :=
    AlignedUnaryListClosure.addedComputableInPolyTime
      encodeInput
      (fun input =>
        UnaryFieldAlternatingPadding.appendZeroValues (first input))
      (fun input =>
        UnaryFieldAlternatingPadding.prependZeroValues (second input))
      (fun input => by
        simp [firstSecond input])
      paddedFirstCompiler paddedSecondCompiler
  unfold selectedValues
  exact UnaryIndexedValueLookup.valuesComputableInPolyTime
    encodeInput
    (fun input => queries (controls input) (first input))
    (fun input => candidateValues (first input) (second input))
    queryCompiler candidateCompiler

end LeanTrominoes.AlignedUnaryBooleanChoice

end
