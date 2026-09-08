/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnaryFieldBooleanFilterCompiler
import LeanTrominoes.TM2EmptyAlphabetListInputCompiler

/-! # Native-list Boolean filtering and aligned block semantics -/

namespace LeanTrominoes.UnaryFieldBooleanFilter
open Computability Turing

/-- Native-list filtering also covers the empty input alphabet. -/
noncomputable def selectedValuesNativeListComputableInPolyTime {Symbol : Type} [Fintype Symbol]
    (controls : List Symbol → List Bool) (values : List Symbol → List Nat)
    (controlCompiler : TM2ComputableInPolyTime id id controls)
    (valueCompiler : TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields values) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (fun input => selectedValues (controls input) (values input)) := by
  classical
  exact if nonemptyAlphabet : Nonempty Symbol then by
    letI : Inhabited Symbol := ⟨Classical.choice nonemptyAlphabet⟩
    exact selectedValuesComputableInPolyTime id controls values controlCompiler valueCompiler
  else by
    letI : IsEmpty Symbol := ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime UnaryFieldEncoderMachine.unaryFields _

theorem selectedValues_append (firstControls secondControls : List Bool)
    (firstValues secondValues : List Nat) (aligned : firstControls.length = firstValues.length) :
    selectedValues (firstControls ++ secondControls) (firstValues ++ secondValues) =
      selectedValues firstControls firstValues ++ selectedValues secondControls secondValues := by
  simp only [selectedValues_eq]
  induction firstControls generalizing firstValues with
  | nil =>
    have empty : firstValues = [] := List.length_eq_zero_iff.mp aligned.symm
    subst firstValues
    rfl
  | cons active firstControls induction =>
    cases firstValues with
    | nil => simp at aligned
    | cons value firstValues =>
      have remaining : firstControls.length = firstValues.length := Nat.succ.inj aligned
      cases active <;> simpa [DelimitedBinaryWordBooleanFilter.selected] using induction firstValues remaining

/-- Filtering concatenated aligned blocks is the concatenation of their filters. -/
theorem selectedValues_flatMap {Block : Type} (blocks : List Block)
    (controls : Block → List Bool) (values : Block → List Nat)
    (aligned : ∀ block ∈ blocks, (controls block).length = (values block).length) :
    selectedValues (blocks.flatMap controls) (blocks.flatMap values) =
      blocks.flatMap (fun block => selectedValues (controls block) (values block)) := by
  induction blocks with
  | nil => rfl
  | cons block blocks induction =>
    rw [List.flatMap_cons, List.flatMap_cons,
      selectedValues_append _ _ _ _ (aligned block (by simp)),
      induction (fun other member => aligned other (by simp [member])), List.flatMap_cons]

theorem selectedValues_length_congr (controls : List Bool) (first second : List Nat)
    (aligned : first.length = second.length) :
    (selectedValues controls first).length = (selectedValues controls second).length := by
  simp only [selectedValues_eq]
  induction controls generalizing first second with
  | nil => rfl
  | cons active controls induction =>
    cases first with
    | nil =>
      have empty : second = [] := List.length_eq_zero_iff.mp aligned.symm
      subst second
      rfl
    | cons value first =>
      cases second with
      | nil => simp at aligned
      | cons other second =>
        have remaining : first.length = second.length := Nat.succ.inj aligned
        cases active <;> simpa [DelimitedBinaryWordBooleanFilter.selected] using induction first second remaining

end LeanTrominoes.UnaryFieldBooleanFilter
