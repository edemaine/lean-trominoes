/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordBooleanFilterCompiler
import LeanTrominoes.DelimitedBinaryWordLengthsCompiler
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.UnaryFieldBinaryWordCompiler

/-! # Boolean filtering of aligned unary fields -/

noncomputable section

namespace LeanTrominoes.UnaryFieldBooleanFilter

open Computability Turing

/-- Retain exactly the unary values whose aligned Boolean controls are true.
Extra controls and extra values are ignored. -/
def selectedValues (controls : List Bool) (values : List Nat) : List Nat :=
  DelimitedBinaryWordLengths.values <|
    DelimitedBinaryWordBooleanFilter.selectedWords controls
      (UnaryFieldBinaryWords.words values)

private theorem selected_map
    {Source Target : Type*} (function : Source → Target)
    (controls : List Bool) (values : List Source) :
    DelimitedBinaryWordBooleanFilter.selected controls
        (values.map function) =
      (DelimitedBinaryWordBooleanFilter.selected controls values).map
        function := by
  induction controls generalizing values with
  | nil => rfl
  | cons active controls induction =>
      cases values with
      | nil => rfl
      | cons value values =>
          cases active <;>
            simp [DelimitedBinaryWordBooleanFilter.selected, induction]

/-- The word-based implementation has the ordinary pointwise filtering
semantics. -/
@[simp] theorem selectedValues_eq
    (controls : List Bool) (values : List Nat) :
    selectedValues controls values =
      DelimitedBinaryWordBooleanFilter.selected controls values := by
  unfold selectedValues DelimitedBinaryWordLengths.values
    DelimitedBinaryWordBooleanFilter.selectedWords
    UnaryFieldBinaryWords.words
  rw [selected_map UnaryFieldBinaryWords.word]
  change
    ((DelimitedBinaryWordBooleanFilter.selected controls values).map
      UnaryFieldBinaryWords.word).map List.length = _
  rw [List.map_map]
  simp [Function.comp_def, UnaryFieldBinaryWords.word]

/-- Any compiled unary column can be filtered by any compiled aligned
Boolean column in polynomial time. -/
noncomputable def selectedValuesComputableInPolyTime
    {Source InputSymbol : Type}
    [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeSource : Source → List InputSymbol)
    (controls : Source → List Bool)
    (values : Source → List Nat)
    (controlCompiler : TM2ComputableInPolyTime encodeSource id controls)
    (valueCompiler : TM2ComputableInPolyTime encodeSource
      UnaryFieldEncoderMachine.unaryFields values) :
    TM2ComputableInPolyTime encodeSource
      UnaryFieldEncoderMachine.unaryFields
      (fun source => selectedValues (controls source) (values source)) := by
  let wordCompiler := TM2CompositionMachine.computableInPolyTime
    valueCompiler UnaryFieldBinaryWords.wordsComputableInPolyTime
  let selectedWordCompiler :=
    DelimitedBinaryWordBooleanFilter.selectedWordsComputableInPolyTime
      encodeSource controls
      (fun source => UnaryFieldBinaryWords.words (values source))
      controlCompiler wordCompiler
  exact TM2CompositionMachine.computableInPolyTime
    selectedWordCompiler
    DelimitedBinaryWordLengths.valuesComputableInPolyTime

end LeanTrominoes.UnaryFieldBooleanFilter

end
