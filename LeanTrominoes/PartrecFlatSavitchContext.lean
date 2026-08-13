/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.IndexedSavitchDFSPartrec
import LeanTrominoes.PartrecDynamicDrop
import LeanTrominoes.PartrecMultiply

/-!
# Locating a flat context after the Savitch DFS stack

`divideEvalProgramList` has seven fixed fields and six fields per continuation
frame.  The suffix-parametric DFS theorem permits a variable-length context to
follow those frames.  This module computes `7 + 6 * frameCount` at runtime and
drops exactly that prefix, recovering the context without packing it into one
natural number.
-/

namespace LeanTrominoes.FiniteState

open Turing ToPartrec

@[simp]
theorem divideFrame_toNatList_length (frame : DivideFrame) :
    frame.toNatList.length = 6 := by
  rcases frame with ⟨depth, first, last, middle, accumulated, leftAnswer⟩
  rfl

@[simp]
theorem divideStackToNatList_length (stack : List DivideFrame) :
    (divideStackToNatList stack).length = 6 * stack.length := by
  induction stack with
  | nil => rfl
  | cons frame stack induction =>
      simp [divideStackToNatList, induction]
      omega

@[simp]
theorem divideEvalProgramList_length
    (context stateCount : Nat) (state : DivideEvalState) :
    (divideEvalProgramList context stateCount state).length =
      7 + 6 * state.stack.length := by
  rcases state with ⟨⟨depth, first, last⟩, stack, answer⟩
  simp [divideEvalProgramList, DivideEvalState.toNatList]
  omega

namespace DivideEvalPartrec

open Code

/-- Assemble `[6, frameCount]` from a serialized DFS state. -/
def flatContextFrameProductArgumentsCode : Code :=
  Code.prepend (Code.numeral 6) (field 2)

def flatContextFrameProductCode : Code :=
  Code.natMultiplyCode.comp flatContextFrameProductArgumentsCode

/-- Compute the number of fields before the appended flat context. -/
def flatContextOffsetCode : Code :=
  (Code.addConst 7).comp flatContextFrameProductCode

@[simp]
theorem flatContextOffsetCode_eval
    (context stateCount : Nat) (state : DivideEvalState)
    (suffix : List Nat) :
    flatContextOffsetCode.eval
        (divideEvalProgramList context stateCount state ++ suffix) =
      pure [7 + 6 * state.stack.length] := by
  have arguments :
      flatContextFrameProductArgumentsCode.eval
          (divideEvalProgramList context stateCount state ++ suffix) =
        pure [6, state.stack.length] := by
    simp [flatContextFrameProductArgumentsCode, field,
      divideEvalProgramList, DivideEvalState.toNatList]
  calc
    _ = (Code.addConst 7).eval [6 * state.stack.length] := by
      simp [flatContextOffsetCode, flatContextFrameProductCode,
        arguments]
    _ = _ := by simp; omega

/-- Prepend the computed offset to the untouched evaluator payload. -/
def flatContextDropInputCode : Code :=
  Code.prepend flatContextOffsetCode Code.id

@[simp]
theorem flatContextDropInputCode_eval
    (context stateCount : Nat) (state : DivideEvalState)
    (suffix : List Nat) :
    flatContextDropInputCode.eval
        (divideEvalProgramList context stateCount state ++ suffix) =
      pure
        ((7 + 6 * state.stack.length) ::
          (divideEvalProgramList context stateCount state ++ suffix)) := by
  simp [flatContextDropInputCode]

/-- Recover the complete native-list context appended after the current DFS
stack. -/
def flatContextCode : Code :=
  Code.dynamicDropCode.comp flatContextDropInputCode

@[simp]
theorem flatContextCode_eval
    (context stateCount : Nat) (state : DivideEvalState)
    (suffix : List Nat) :
    flatContextCode.eval
        (divideEvalProgramList context stateCount state ++ suffix) =
      pure suffix := by
  have prefixLength := divideEvalProgramList_length context stateCount state
  simp [flatContextCode, prefixLength]

end DivideEvalPartrec
end LeanTrominoes.FiniteState
