/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteRecordMachine

/-! # Tape-update identities for the route-record machine -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace GadgetSparseRouteRecordMachine

@[simp] theorem update_tapes_input (data : TapeData)
    (value : List InputToken) :
    Function.update (tapes data) Stack.input value =
      tapes { data with input := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_horizontal (data : TapeData)
    (value : List Unit) :
    Function.update (tapes data) Stack.horizontal value =
      tapes { data with horizontal := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_horizontalComplement (data : TapeData)
    (value : List Unit) :
    Function.update (tapes data) Stack.horizontalComplement value =
      tapes { data with horizontalComplement := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_verticalPositive (data : TapeData)
    (value : List Unit) :
    Function.update (tapes data) Stack.verticalPositive value =
      tapes { data with verticalPositive := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_verticalNegative (data : TapeData)
    (value : List Unit) :
    Function.update (tapes data) Stack.verticalNegative value =
      tapes { data with verticalNegative := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_scratch (data : TapeData)
    (value : List Unit) :
    Function.update (tapes data) Stack.scratch value =
      tapes { data with scratch := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_outputReverse (data : TapeData)
    (value : List OutputToken) :
    Function.update (tapes data) Stack.outputReverse value =
      tapes { data with outputReverse := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_output (data : TapeData)
    (value : List OutputToken) :
    Function.update (tapes data) Stack.output value =
      tapes { data with output := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

end GadgetSparseRouteRecordMachine
end LeanTrominoes
