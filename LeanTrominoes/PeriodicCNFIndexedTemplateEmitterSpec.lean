/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPolySpaceInitialTailPadding

/-!
# Data-indexed affine template emission

Unlike the earlier affine emitter, the initial source-stack prefix must choose
a different fixed atom base for each finite source symbol.  This specification
therefore assigns each selected input item an optional affine recipe list and
evaluates that recipe at the item's zero-based selected position.  Unselected
items neither emit tokens nor advance the position.
-/

namespace LeanTrominoes
namespace PeriodicCNF
namespace IndexedTemplateEmitter

open AffineTemplateEmitterMachine
open UnaryProgramTokens

/-- A finite input item either contributes one affine recipe block or is
ignored. -/
abbrev Family (Data : Type) := Data → Option (List Recipe)

def selected {Data : Type} (family : Family Data) (data : Data) : Bool :=
  (family data).isSome

def selectedCount {Data : Type} (family : Family Data) :
    List Data → Nat
  | [] => 0
  | data :: datas =>
      (if (family data).isSome then 1 else 0) + selectedCount family datas

/-- Emit from left to right, evaluating each selected item's recipe at the
number of earlier selected items. -/
def emittedAux {Data : Type} (family : Family Data) :
    Nat → List Data → List Token
  | _, [] => []
  | position, data :: datas =>
      match family data with
      | none => emittedAux family position datas
      | some recipes =>
          positionTokens recipes position ++
            emittedAux family (position + 1) datas

def emitted {Data : Type} (family : Family Data) (data : List Data) :
    List Token :=
  emittedAux family 0 data

@[simp]
theorem selectedCount_nil {Data : Type} (family : Family Data) :
    selectedCount family [] = 0 :=
  rfl

@[simp]
theorem selectedCount_cons_none {Data : Type} (family : Family Data)
    (data : Data) (datas : List Data) (none : family data = none) :
    selectedCount family (data :: datas) = selectedCount family datas := by
  simp [selectedCount, none]

@[simp]
theorem selectedCount_cons_some {Data : Type} (family : Family Data)
    (data : Data) (datas : List Data) (recipes : List Recipe)
    (some : family data = some recipes) :
    selectedCount family (data :: datas) =
      selectedCount family datas + 1 := by
  simp [selectedCount, some]
  omega

theorem selectedCount_append {Data : Type} (family : Family Data)
    (first second : List Data) :
    selectedCount family (first ++ second) =
      selectedCount family first + selectedCount family second := by
  induction first with
  | nil => simp [selectedCount]
  | cons data first induction =>
      cases value : family data with
      | none => simp [selectedCount, value, induction]
      | some recipes =>
          simp [selectedCount, value, induction, Nat.add_assoc]
          omega

@[simp]
theorem emittedAux_cons_none {Data : Type} (family : Family Data)
    (position : Nat) (data : Data) (datas : List Data)
    (none : family data = none) :
    emittedAux family position (data :: datas) =
      emittedAux family position datas := by
  simp [emittedAux, none]

@[simp]
theorem emittedAux_cons_some {Data : Type} (family : Family Data)
    (position : Nat) (data : Data) (datas : List Data)
    (recipes : List Recipe) (some : family data = some recipes) :
    emittedAux family position (data :: datas) =
      positionTokens recipes position ++
        emittedAux family (position + 1) datas := by
  simp [emittedAux, some]

/-- Splitting an input advances the second half by exactly the selected count
of the first half. -/
theorem emittedAux_append {Data : Type} (family : Family Data)
    (position : Nat) (first second : List Data) :
    emittedAux family position (first ++ second) =
      emittedAux family position first ++
        emittedAux family (position + selectedCount family first) second := by
  induction first generalizing position with
  | nil => simp [emittedAux, selectedCount]
  | cons data first induction =>
      cases value : family data with
      | none =>
          simp only [List.cons_append, emittedAux_cons_none family _ _ _ value,
            selectedCount_cons_none family _ _ value]
          exact induction position
      | some recipes =>
          simp only [List.cons_append,
            emittedAux_cons_some family _ _ _ recipes value,
            selectedCount_cons_some family _ _ recipes value,
            List.append_assoc]
          rw [induction]
          have positionEq :
              position + 1 + selectedCount family first =
                position + (selectedCount family first + 1) := by
            omega
          rw [positionEq]

theorem selectedCount_eq_zero_of_none {Data : Type} (family : Family Data)
    (data : List Data) (none : ∀ item ∈ data, family item = none) :
    selectedCount family data = 0 := by
  induction data with
  | nil => rfl
  | cons item data induction =>
      rw [selectedCount_cons_none family item data (none item (by simp))]
      exact induction fun tail membership => none tail (by simp [membership])

theorem emittedAux_eq_nil_of_none {Data : Type} (family : Family Data)
    (position : Nat) (data : List Data)
    (none : ∀ item ∈ data, family item = none) :
    emittedAux family position data = [] := by
  induction data generalizing position with
  | nil => rfl
  | cons item data induction =>
      rw [emittedAux_cons_none family position item data
        (none item (by simp))]
      exact induction position fun tail membership =>
        none tail (by simp [membership])

/-- A completely ignored suffix has no effect on emission. -/
theorem emittedAux_append_none {Data : Type} (family : Family Data)
    (position : Nat) (first second : List Data)
    (none : ∀ item ∈ second, family item = none) :
    emittedAux family position (first ++ second) =
      emittedAux family position first := by
  rw [emittedAux_append,
    emittedAux_eq_nil_of_none family _ second none, List.append_nil]

end IndexedTemplateEmitter
end PeriodicCNF
end LeanTrominoes
