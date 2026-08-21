/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairProductMachine

/-! # Tape-update identities for the binary-word product machine -/

namespace LeanTrominoes
namespace DelimitedBinaryWordPairProductMachine

@[simp] theorem update_tapes_input (data : TapeData)
    (value : List WordToken) :
    Function.update (tapes data) Stack.input value =
      tapes { data with input := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_reverse (data : TapeData)
    (value : List WordToken) :
    Function.update (tapes data) Stack.reverse value =
      tapes { data with reverse := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_outer (data : TapeData)
    (value : List WordToken) :
    Function.update (tapes data) Stack.outer value =
      tapes { data with outer := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_source (data : TapeData)
    (value : List WordToken) :
    Function.update (tapes data) Stack.source value =
      tapes { data with source := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_first (data : TapeData)
    (value : List Bool) :
    Function.update (tapes data) Stack.first value =
      tapes { data with first := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_firstOriginal (data : TapeData)
    (value : List Bool) :
    Function.update (tapes data) Stack.firstOriginal value =
      tapes { data with firstOriginal := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_sourceRestore (data : TapeData)
    (value : List WordToken) :
    Function.update (tapes data) Stack.sourceRestore value =
      tapes { data with sourceRestore := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_outputReverse (data : TapeData)
    (value : List PairToken) :
    Function.update (tapes data) Stack.outputReverse value =
      tapes { data with outputReverse := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_output (data : TapeData)
    (value : List PairToken) :
    Function.update (tapes data) Stack.output value =
      tapes { data with output := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

end DelimitedBinaryWordPairProductMachine
end LeanTrominoes
