/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFMachineClock

/-!
# Reconstructing bounded machine configurations

A structurally well-formed Boolean slice stores each stack as a fixed-width
vector of optional symbols.  This file turns the occupied prefix of that
vector back into an ordinary TM2 stack and proves that every represented cell
is preserved.  Thus the decoded finite slice can be compared directly with
Mathlib's existing TM2 step semantics.
-/

noncomputable section

namespace LeanTrominoes

namespace PeriodicCNF

open Turing

namespace BoundedMachineAtom

/-- Read the initial `some` prefix of a fixed-width optional vector as a list.
The first `none` terminates the list. -/
def occupiedPrefix {Symbol : Type*} :
    (width : Nat) → (Fin width → Option Symbol) → List Symbol
  | 0, _ => []
  | width + 1, cells =>
      match cells 0 with
      | none => []
      | some symbol =>
          symbol :: occupiedPrefix width (fun position => cells position.succ)

/-- Once a cell is empty, the immediately following cell is empty too. -/
def OptionVectorShaped {Symbol : Type*} {width : Nat}
    (cells : Fin width → Option Symbol) : Prop :=
  ∀ (index : Nat) (nextExists : index + 1 < width),
    cells ⟨index, Nat.lt_of_succ_lt nextExists⟩ = none →
      cells ⟨index + 1, nextExists⟩ = none

theorem optionVectorShaped_tail {Symbol : Type*} {width : Nat}
    {cells : Fin (width + 1) → Option Symbol}
    (shaped : OptionVectorShaped cells) :
    OptionVectorShaped (fun position : Fin width => cells position.succ) := by
  intro index nextExists currentNone
  exact shaped (index + 1) (by omega) currentNone

theorem optionVectorShaped_none_of_head_none {Symbol : Type*} {width : Nat}
    {cells : Fin (width + 1) → Option Symbol}
    (shaped : OptionVectorShaped cells) (headNone : cells 0 = none)
    (position : Fin (width + 1)) :
    cells position = none := by
  have allNone : ∀ (index : Nat) (indexExists : index < width + 1),
      cells ⟨index, indexExists⟩ = none := by
    intro index
    induction index with
    | zero =>
        intro indexExists
        simpa using headNone
    | succ index ih =>
        intro indexExists
        apply shaped index indexExists
        exact ih (Nat.lt_of_succ_lt indexExists)
  exact allNone position.val position.isLt

/-- A suffix-shaped vector is exactly the optional-cell view of its occupied
prefix at every in-range position. -/
theorem occupiedPrefix_getElem?_eq {Symbol : Type*} {width : Nat}
    (cells : Fin width → Option Symbol)
    (shaped : OptionVectorShaped cells) (position : Fin width) :
    (occupiedPrefix width cells)[position.val]? = cells position := by
  induction width with
  | zero => exact Fin.elim0 position
  | succ width ih =>
      cases headValue : cells 0 with
      | none =>
          rw [occupiedPrefix, headValue]
          simp only [List.getElem?_nil]
          exact (optionVectorShaped_none_of_head_none shaped headValue position).symm
      | some symbol =>
          refine Fin.cases ?_ (fun tailPosition => ?_) position
          · simp [occupiedPrefix, headValue]
          · simpa [occupiedPrefix, headValue] using
              ih (fun tailPosition : Fin width => cells tailPosition.succ)
                (optionVectorShaped_tail shaped) tailPosition

theorem occupiedPrefix_length_le {Symbol : Type*} (width : Nat)
    (cells : Fin width → Option Symbol) :
    (occupiedPrefix width cells).length ≤ width := by
  induction width with
  | zero => rfl
  | succ width ih =>
      cases headValue : cells 0 <;>
        simp [occupiedPrefix, headValue, ih]

/-- If every in-range optional cell comes from a bounded list, recovering its
occupied prefix returns that list exactly. -/
theorem occupiedPrefix_eq_list {Symbol : Type*} {width : Nat}
    (cells : Fin width → Option Symbol) (shaped : OptionVectorShaped cells)
    (symbols : List Symbol) (symbolsFit : symbols.length ≤ width)
    (cellsEq : ∀ position : Fin width,
      cells position = symbols[position.val]?) :
    occupiedPrefix width cells = symbols := by
  apply List.ext_getElem?
  intro index
  by_cases indexInRange : index < width
  · let position : Fin width := ⟨index, indexInRange⟩
    rw [occupiedPrefix_getElem?_eq cells shaped position]
    exact cellsEq position
  · have widthLe : width ≤ index := Nat.not_lt.mp indexInRange
    rw [List.getElem?_eq_none
        (le_trans (occupiedPrefix_length_le width cells) widthLe),
      List.getElem?_eq_none (le_trans symbolsFit widthLe)]

variable {tm : FinTM2} {space clockBits : Nat}

/-- Recover one ordinary TM2 stack from its fixed-width optional cells. -/
def BoundedMachineSlice.stackList
    (slice : BoundedMachineSlice tm space clockBits) (stack : tm.K) :
    List (tm.Γ stack) :=
  occupiedPrefix space (slice.stack stack)

/-- Forget the reset clock and reconstruct the ordinary TM2 configuration
represented by a bounded slice. -/
def BoundedMachineSlice.toCfg
    (slice : BoundedMachineSlice tm space clockBits) : tm.Cfg where
  l := slice.label
  var := slice.control
  stk := slice.stackList

/-- Interpret the slice's fixed-width little-endian clock bits. -/
def BoundedMachineSlice.clockValue
    (slice : BoundedMachineSlice tm space clockBits) : Nat :=
  TransitionExpr.bitsValue ((List.finRange clockBits).map slice.clock)

/-- Reconstruct the complete semantic reset-clock state represented by a
bounded Boolean slice. -/
def BoundedMachineSlice.toResetClockState
    (slice : BoundedMachineSlice tm space clockBits) :
    PeriodicComputation.ResetClockState tm.Cfg where
  clock := slice.clockValue
  config := slice.toCfg

theorem BoundedMachineSlice.stack_optionVectorShaped
    {slice : BoundedMachineSlice tm space clockBits}
    (shaped : slice.StackShaped) (stack : tm.K) :
    OptionVectorShaped (slice.stack stack) :=
  shaped stack

@[simp]
theorem BoundedMachineSlice.toCfg_label
    (slice : BoundedMachineSlice tm space clockBits) :
    slice.toCfg.l = slice.label :=
  rfl

@[simp]
theorem BoundedMachineSlice.toCfg_control
    (slice : BoundedMachineSlice tm space clockBits) :
    slice.toCfg.var = slice.control :=
  rfl

/-- Reconstructing a list-shaped slice preserves every represented stack
cell, including the empty suffix. -/
theorem BoundedMachineSlice.toCfg_stack_getElem?_eq
    {slice : BoundedMachineSlice tm space clockBits}
    (shaped : slice.StackShaped) (stack : tm.K) (position : Fin space) :
    (slice.toCfg.stk stack)[position.val]? = slice.stack stack position := by
  exact occupiedPrefix_getElem?_eq _
    (slice.stack_optionVectorShaped shaped stack) position

theorem BoundedMachineSlice.toCfg_stack_length_le
    (slice : BoundedMachineSlice tm space clockBits) (stack : tm.K) :
    (slice.toCfg.stk stack).length ≤ space :=
  occupiedPrefix_length_le space (slice.stack stack)

variable [stackFinite : ∀ stack, Fintype (tm.Γ stack)]

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

/-- Canonical one-hot fields decode to the original label. -/
theorem decode_encode_label
    (state : PeriodicComputation.ResetClockState tm.Cfg) :
    (decode (tm := tm) (space := space) (clockBits := clockBits)
      (encode (space := space) (clockBits := clockBits) state)).label =
        state.config.l := by
  have recovered := decode_label_bit
    (oneHotFields_encode (space := space) (clockBits := clockBits) state)
    state.config.l
  simpa using recovered.symm

/-- Canonical one-hot fields decode to the original finite control state. -/
theorem decode_encode_control
    (state : PeriodicComputation.ResetClockState tm.Cfg) :
    (decode (tm := tm) (space := space) (clockBits := clockBits)
      (encode (space := space) (clockBits := clockBits) state)).control =
        state.config.var := by
  have recovered := decode_state_bit
    (oneHotFields_encode (space := space) (clockBits := clockBits) state)
    state.config.var
  simpa using recovered.symm

/-- Canonical one-hot fields decode every represented stack cell. -/
theorem decode_encode_stack
    (state : PeriodicComputation.ResetClockState tm.Cfg)
    (stack : tm.K) (position : Fin space) :
    (decode (tm := tm) (space := space) (clockBits := clockBits)
      (encode (space := space) (clockBits := clockBits) state)).stack
        stack position = (state.config.stk stack)[position.val]? := by
  have recovered := decode_stack_bit
    (oneHotFields_encode (space := space) (clockBits := clockBits) state)
    stack position (state.config.stk stack)[position.val]?
  simpa using recovered.symm

/-- The fixed-width clock of a canonical encoding decodes to its semantic
clock whenever that clock fits in the chosen width. -/
theorem decode_encode_clockValue
    (state : PeriodicComputation.ResetClockState tm.Cfg)
    (clockFits : state.clock < 2 ^ clockBits) :
    (decode (tm := tm) (space := space) (clockBits := clockBits)
      (encode (space := space) (clockBits := clockBits) state)).clockValue =
        state.clock := by
  have bitsEq :
      (List.finRange clockBits).map
          (decode (tm := tm) (space := space) (clockBits := clockBits)
            (encode (space := space) (clockBits := clockBits) state)).clock =
        (clockAtoms (tm := tm) (space := space)
          (clockBits := clockBits)).map
            (encode (space := space) (clockBits := clockBits) state) := by
    simp [clockAtoms, List.map_map, Function.comp_def]
  rw [BoundedMachineSlice.clockValue, bitsEq]
  exact bitsValue_clockAtoms_encode (space := space)
    (clockBits := clockBits) state clockFits

/-- Reconstructing a canonical slice whose stacks fit in the selected width
returns the original TM2 configuration. -/
theorem toCfg_decode_encode
    (state : PeriodicComputation.ResetClockState tm.Cfg)
    (stacksFit : ∀ stack, (state.config.stk stack).length ≤ space) :
    (decode (tm := tm) (space := space) (clockBits := clockBits)
      (encode (space := space) (clockBits := clockBits) state)).toCfg =
        state.config := by
  let slice := decode (tm := tm) (space := space) (clockBits := clockBits)
    (encode (space := space) (clockBits := clockBits) state)
  have shaped : slice.StackShaped := by
    exact decode_stackShaped
      (oneHotFields_encode (space := space) (clockBits := clockBits) state)
      (stackSuffixFields_encode (space := space) (clockBits := clockBits) state)
  change slice.toCfg = state.config
  cases configEq : state.config with
  | mk label control stackContents =>
      change Turing.TM2.Cfg.mk slice.label slice.control slice.stackList =
        Turing.TM2.Cfg.mk label control stackContents
      congr 1
      · simpa [configEq] using decode_encode_label state
      · simpa [configEq] using decode_encode_control state
      · funext stack
        simpa [BoundedMachineSlice.stackList, configEq] using
          occupiedPrefix_eq_list (slice.stack stack)
            (slice.stack_optionVectorShaped shaped stack)
            (state.config.stk stack) (stacksFit stack)
            (decode_encode_stack state stack)

/-- The complete semantic state is a left inverse of canonical encoding on
bounded stacks and in-range clocks. -/
theorem toResetClockState_decode_encode
    (state : PeriodicComputation.ResetClockState tm.Cfg)
    (clockFits : state.clock < 2 ^ clockBits)
    (stacksFit : ∀ stack, (state.config.stk stack).length ≤ space) :
    (decode (tm := tm) (space := space) (clockBits := clockBits)
      (encode (space := space) (clockBits := clockBits) state)).toResetClockState =
        state := by
  cases state with
  | mk clock config =>
      change PeriodicComputation.ResetClockState.mk _ _ =
        PeriodicComputation.ResetClockState.mk clock config
      congr 1
      · exact decode_encode_clockValue ⟨clock, config⟩ clockFits
      · exact toCfg_decode_encode ⟨clock, config⟩ stacksFit

end BoundedMachineAtom

end PeriodicCNF

end LeanTrominoes
