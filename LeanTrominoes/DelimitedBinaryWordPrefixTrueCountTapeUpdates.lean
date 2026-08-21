/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/

import LeanTrominoes.DelimitedBinaryWordPrefixTrueCountMachine

/-! # Tape-update identities for row-prefix true counts -/

namespace LeanTrominoes
namespace DelimitedBinaryWordPrefixTrueCountMachine

@[simp] theorem update_tapes_input (data : TapeData) (value : List Token) :
    Function.update (tapes data) Stack.input value =
      tapes { data with input := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_rowIndex
    (data : TapeData) (value : List Unit) :
    Function.update (tapes data) Stack.rowIndex value =
      tapes { data with rowIndex := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_indexRestore
    (data : TapeData) (value : List Unit) :
    Function.update (tapes data) Stack.indexRestore value =
      tapes { data with indexRestore := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_prefixCountdown
    (data : TapeData) (value : List Unit) :
    Function.update (tapes data) Stack.prefixCountdown value =
      tapes { data with prefixCountdown := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_outputReverse
    (data : TapeData) (value : List OutputSymbol) :
    Function.update (tapes data) Stack.outputReverse value =
      tapes { data with outputReverse := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_output
    (data : TapeData) (value : List OutputSymbol) :
    Function.update (tapes data) Stack.output value =
      tapes { data with output := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

end DelimitedBinaryWordPrefixTrueCountMachine
end LeanTrominoes
