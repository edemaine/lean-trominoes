/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/

import LeanTrominoes.UnaryPrefixSumsMachine

/-! # Tape-update identities for the unary prefix-sum machine -/

namespace LeanTrominoes
namespace UnaryPrefixSumsMachine

@[simp] theorem update_tapes_input (data : TapeData) (value : List Symbol) :
    Function.update (tapes data) Stack.input value =
      tapes { data with input := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_sum (data : TapeData) (value : List Symbol) :
    Function.update (tapes data) Stack.sum value =
      tapes { data with sum := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_sumRestore
    (data : TapeData) (value : List Symbol) :
    Function.update (tapes data) Stack.sumRestore value =
      tapes { data with sumRestore := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_outputReverse
    (data : TapeData) (value : List Symbol) :
    Function.update (tapes data) Stack.outputReverse value =
      tapes { data with outputReverse := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_output
    (data : TapeData) (value : List Symbol) :
    Function.update (tapes data) Stack.output value =
      tapes { data with output := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

end UnaryPrefixSumsMachine
end LeanTrominoes
