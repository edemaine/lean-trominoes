/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFMachineAtoms
import LeanTrominoes.PeriodicComputationCycle

/-!
# Boolean valuations of bounded machine configurations

This file gives every bounded clocked TM2 configuration its canonical Boolean
slice valuation.  Optional labels, finite control states, and optional stack
cell symbols are represented one-hot; clock bits use the little-endian order
from `BoundedMachineAtom.clockAtoms`.
-/

noncomputable section

namespace LeanTrominoes

namespace PeriodicCNF

open Turing
open PeriodicComputation

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

namespace BoundedMachineAtom

variable {tm : FinTM2} {space clockBits : Nat}
variable [stackFinite : ∀ stack, Fintype (tm.Γ stack)]

noncomputable local instance : DecidableEq tm.Λ := Classical.decEq _
noncomputable local instance : DecidableEq tm.σ := Classical.decEq _
noncomputable local instance (stack : tm.K) : DecidableEq (tm.Γ stack) :=
  Classical.decEq _

/-- Boolean meaning of one typed atom in a bounded clocked configuration. -/
noncomputable def value (state : ResetClockState tm.Cfg)
    (atom : BoundedMachineAtom tm space clockBits) : Bool := by
  classical
  exact match atom with
    | .label labelValue => decide (state.config.l = labelValue)
    | .state control => decide (state.config.var = control)
    | .stack ⟨stackIndex, position, symbol⟩ =>
        decide ((state.config.stk stackIndex)[position.val]? = symbol)
    | .clock position => state.clock.testBit position.val

@[simp]
theorem value_label (state : ResetClockState tm.Cfg)
    (labelValue : Option tm.Λ) :
    value (space := space) (clockBits := clockBits) state (.label labelValue) =
      decide (state.config.l = labelValue) := by
  simp [value]

@[simp]
theorem value_state (state : ResetClockState tm.Cfg) (control : tm.σ) :
    value (space := space) (clockBits := clockBits) state (.state control) =
      decide (state.config.var = control) := by
  simp [value]

@[simp]
theorem value_stack (state : ResetClockState tm.Cfg)
    (stack : tm.K) (position : Fin space) (symbol : Option (tm.Γ stack)) :
    value (clockBits := clockBits) state (.stack ⟨stack, position, symbol⟩) =
      decide ((state.config.stk stack)[position.val]? = symbol) := by
  simp [value]

@[simp]
theorem value_clock (state : ResetClockState tm.Cfg)
    (position : Fin clockBits) :
    value (space := space) state (.clock position) =
      state.clock.testBit position.val := by
  simp [value]

/-- Canonical natural-atom valuation of a bounded clocked configuration.
Names beyond the finite source interval are false. -/
def encode (state : ResetClockState tm.Cfg) (atom : Nat) : Bool :=
  if atomLt : atom < atomCount (tm := tm) (space := space)
      (clockBits := clockBits) then
    value state ((atomEquivFin (tm := tm) (space := space)
      (clockBits := clockBits)).symm ⟨atom, atomLt⟩)
  else
    false

@[simp]
theorem encode_code (state : ResetClockState tm.Cfg)
    (atom : BoundedMachineAtom tm space clockBits) :
    encode (space := space) (clockBits := clockBits) state (code atom) =
      value state atom := by
  rw [encode, dif_pos (code_lt_atomCount atom)]
  simp only [code]
  rw [Equiv.symm_apply_apply]

@[simp]
theorem encode_label (state : ResetClockState tm.Cfg)
    (label : Option tm.Λ) :
    encode (space := space) (clockBits := clockBits) state
        (code (.label label : BoundedMachineAtom tm space clockBits)) =
      decide (state.config.l = label) := by
  rw [encode_code]
  rfl

@[simp]
theorem encode_state (state : ResetClockState tm.Cfg)
    (control : tm.σ) :
    encode (space := space) (clockBits := clockBits) state
        (code (.state control : BoundedMachineAtom tm space clockBits)) =
      decide (state.config.var = control) := by
  rw [encode_code]
  rfl

@[simp]
theorem encode_stack (state : ResetClockState tm.Cfg)
    (stack : tm.K) (position : Fin space) (symbol : Option (tm.Γ stack)) :
    encode (space := space) (clockBits := clockBits) state
        (code (.stack ⟨stack, position, symbol⟩ :
          BoundedMachineAtom tm space clockBits)) =
      decide ((state.config.stk stack)[position.val]? = symbol) := by
  rw [encode_code]
  rfl

@[simp]
theorem encode_clock (state : ResetClockState tm.Cfg)
    (position : Fin clockBits) :
    encode (space := space) (clockBits := clockBits) state
        (code (.clock position : BoundedMachineAtom tm space clockBits)) =
      state.clock.testBit position.val := by
  rw [encode_code]
  rfl

private theorem exactlyOneTrue_decide_eq {Value : Type*}
    [DecidableEq Value] {target : Value} {values : List Value}
    (nodup : values.Nodup) (member : target ∈ values) :
    TransitionExpr.ExactlyOneTrue
      (values.map fun value => decide (target = value)) := by
  induction values with
  | nil => simp at member
  | cons head tail ih =>
      have headNotMem := List.nodup_cons.mp nodup
      by_cases targetHead : target = head
      · subst target
        rw [List.map_cons]
        left
        refine ⟨by simp, ?_⟩
        intro bit bitMem
        obtain ⟨value, valueMem, rfl⟩ := List.mem_map.mp bitMem
        have unequal : head ≠ value := by
          intro equality
          apply headNotMem.1
          simpa [equality] using valueMem
        simp [unequal]
      · rw [List.map_cons]
        right
        refine ⟨by simp [targetHead], ih headNotMem.2 ?_⟩
        simpa [targetHead] using member

theorem encoded_label_exactlyOne (state : ResetClockState tm.Cfg) :
    TransitionExpr.ExactlyOneTrue
      ((labelAtoms (tm := tm) (space := space) (clockBits := clockBits)).map
        (encode (space := space) (clockBits := clockBits) state)) := by
  classical
  simpa [labelAtoms, Function.comp_def] using
    exactlyOneTrue_decide_eq
      (finiteValues_nodup (Option tm.Λ))
      (mem_finiteValues state.config.l)

theorem encoded_state_exactlyOne (state : ResetClockState tm.Cfg) :
    TransitionExpr.ExactlyOneTrue
      ((stateAtoms (tm := tm) (space := space) (clockBits := clockBits)).map
        (encode (space := space) (clockBits := clockBits) state)) := by
  classical
  simpa [stateAtoms, Function.comp_def] using
    exactlyOneTrue_decide_eq
      (finiteValues_nodup tm.σ)
      (mem_finiteValues state.config.var)

theorem encoded_stack_exactlyOne (state : ResetClockState tm.Cfg)
    (stack : tm.K) (position : Fin space) :
    TransitionExpr.ExactlyOneTrue
      ((stackCellAtoms (tm := tm) (clockBits := clockBits) stack position).map
        (encode (space := space) (clockBits := clockBits) state)) := by
  classical
  simpa [stackCellAtoms, Function.comp_def] using
    exactlyOneTrue_decide_eq
      (finiteValues_nodup (Option (tm.Γ stack)))
      (mem_finiteValues ((state.config.stk stack)[position.val]?))

/-- Exact-one expressions for every finite field in a bounded configuration.
Clock bits are ordinary binary bits and therefore need no exact-one clause. -/
def oneHotFieldExpressions : List TransitionExpr :=
  [TransitionExpr.currentExactlyOne
      (labelAtoms (tm := tm) (space := space) (clockBits := clockBits)),
    TransitionExpr.currentExactlyOne
      (stateAtoms (tm := tm) (space := space) (clockBits := clockBits))] ++
    (finiteValues tm.K).flatMap fun stack =>
      (List.finRange space).map fun position =>
        TransitionExpr.currentExactlyOne
          (stackCellAtoms (tm := tm) (clockBits := clockBits)
            stack position)

/-- Structural exact-one constraint for a bounded configuration slice. -/
def oneHotFields : TransitionExpr :=
  TransitionExpr.all
    (oneHotFieldExpressions (tm := tm) (space := space)
      (clockBits := clockBits))

/-- Every canonical bounded configuration valuation satisfies all exact-one
field constraints. -/
theorem oneHotFields_encode (state : ResetClockState tm.Cfg) :
    (oneHotFields (tm := tm) (space := space) (clockBits := clockBits)).eval
        (encode (space := space) (clockBits := clockBits) state)
        (encode (space := space) (clockBits := clockBits) state) = true := by
  rw [oneHotFields, TransitionExpr.all_eval, List.all_eq_true]
  intro expression expressionMem
  rw [oneHotFieldExpressions, List.mem_append] at expressionMem
  rcases expressionMem with expressionMem | expressionMem
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at expressionMem
    rcases expressionMem with rfl | rfl
    · exact (TransitionExpr.currentExactlyOne_eval_iff _ _ _).mpr
        (encoded_label_exactlyOne state)
    · exact (TransitionExpr.currentExactlyOne_eval_iff _ _ _).mpr
        (encoded_state_exactlyOne state)
  · rw [List.mem_flatMap] at expressionMem
    obtain ⟨stack, _, expressionMem⟩ := expressionMem
    obtain ⟨position, _, rfl⟩ := List.mem_map.mp expressionMem
    exact (TransitionExpr.currentExactlyOne_eval_iff _ _ _).mpr
      (encoded_stack_exactlyOne state stack position)

theorem oneHotFields_atomsBelow :
    (oneHotFields (tm := tm) (space := space) (clockBits := clockBits)).AtomsBelow
      (atomCount (tm := tm) (space := space) (clockBits := clockBits)) := by
  apply TransitionExpr.all_atomsBelow
  intro expression expressionMem
  rw [oneHotFieldExpressions, List.mem_append] at expressionMem
  rcases expressionMem with expressionMem | expressionMem
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at expressionMem
    rcases expressionMem with rfl | rfl
    · exact TransitionExpr.currentExactlyOne_atomsBelow labelAtoms_below
    · exact TransitionExpr.currentExactlyOne_atomsBelow stateAtoms_below
  · rw [List.mem_flatMap] at expressionMem
    obtain ⟨stack, _, expressionMem⟩ := expressionMem
    obtain ⟨position, _, rfl⟩ := List.mem_map.mp expressionMem
    exact TransitionExpr.currentExactlyOne_atomsBelow
      (stackCellAtoms_below stack position)

end BoundedMachineAtom

end PeriodicCNF

end LeanTrominoes
