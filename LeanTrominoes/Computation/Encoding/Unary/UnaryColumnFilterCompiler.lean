/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Computation.Encoding.Unary.UnaryColumnSignedEncoding
import LeanTrominoes.Computation.Encoding.Unary.UnaryFieldBooleanFilterNativeListCompiler
import LeanTrominoes.Tiling.Tromino.Finite.FiniteIndexSlotUnaryDecoderCompiler
import LeanTrominoes.Computation.Encoding.Finite.FiniteBlockTransducer

/-! # Filtering aligned unary columns by compiled finite controls -/
noncomputable section
namespace LeanTrominoes.UnaryColumn
open Computability Turing

private theorem selected_filter_map {Row : Type} (rows : List Row) (predicate : Row → Bool) (value : Row → Nat) :
    UnaryFieldBooleanFilter.selectedValues (rows.map predicate) (rows.map value) =
      (rows.filter predicate).map value := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    cases active : predicate row <;>
      simpa [UnaryFieldBooleanFilter.selectedValues_eq,DelimitedBinaryWordBooleanFilter.selected,active] using ih

variable {Symbol Row : Type} [Fintype Symbol] [Inhabited Symbol]
  {rows : List Symbol → List Row} {predicate : List Symbol → Row → Bool}
  {value weight : List Symbol → Row → Nat}

def filtered (controls : TM2ComputableInPolyTime id id (fun s => (rows s).map (predicate s)))
    (values : Compiler rows value) : Compiler (fun s => (rows s).filter (predicate s)) value := by
  let physical := UnaryFieldBooleanFilter.selectedValuesComputableInPolyTime id
    (fun s => (rows s).map (predicate s)) (fun s => (rows s).map (value s)) controls values
  exact TM2ComputableInPolyTime.of_eq physical (fun s => selected_filter_map _ _ _)

def threeControls (values : List Nat) : List Bool := values.map fun value => decide (value = 3)

def threeControlsCompiler : TM2ComputableInPolyTime UnaryFieldEncoderMachine.unaryFields id threeControls := by
  let physical := TM2CompositionMachine.computableInPolyTime (FiniteIndexSlotUnaryDecoder.computableInPolyTime 1)
    (FiniteBlockTransducer.computableInPolyTime (fun code : FiniteIndexSlotUnaryDecoder.Pair 1 => [code.2.val == 3]))
  apply TM2ComputableInPolyTime.of_eq physical
  intro values
  simp only [FiniteIndexSlotUnaryDecoder.pairs,List.flatMap_map]
  change values.flatMap (fun value => [(FiniteIndexSlotUnaryDecoder.boundedCode 1 value).2.val == 3]) = _
  have equality (value : Nat) : ((FiniteIndexSlotUnaryDecoder.boundedCode 1 value).2.val == 3) = decide (value = 3) := by
    simp only [FiniteIndexSlotUnaryDecoder.boundedCode,FiniteIndexSlotUnaryDecoder.codeBound]
    by_cases same : value = 3
    · subst value; rfl
    · have different : min value 7 % 8 ≠ 3 := by omega
      simp [same,different]
  simp only [equality,threeControls]
  induction values with
  | nil => rfl
  | cons value values ih => simpa using ih

def filterThree (weights : Compiler rows weight) (values : Compiler rows value) :
    Compiler (fun s => (rows s).filter fun row => weight s row = 3) value := by
  let controls := TM2CompositionMachine.computableInPolyTime weights threeControlsCompiler
  apply filtered (predicate := fun s row => decide (weight s row = 3)) _ values
  exact TM2ComputableInPolyTime.of_eq controls (fun s => by simp [threeControls,List.map_map])

end LeanTrominoes.UnaryColumn
end
