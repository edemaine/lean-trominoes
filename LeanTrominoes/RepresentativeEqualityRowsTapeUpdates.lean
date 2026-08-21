/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RepresentativeEqualityRowsMachine

/-! # Tape-update identities for the representative equality-row machine -/

namespace LeanTrominoes
namespace RepresentativeEqualityRowsMachine

@[simp] theorem update_input (data : TapeData) (value : List Token) :
    Function.update (tapes data) .input value =
      tapes { data with input := value } := by
  funext stack
  cases stack <;> simp [tapes]

@[simp] theorem update_rowIndex (data : TapeData) (value : List Unit) :
    Function.update (tapes data) .rowIndex value =
      tapes { data with rowIndex := value } := by
  funext stack
  cases stack <;> simp [tapes]

@[simp] theorem update_indexRestore (data : TapeData)
    (value : List Unit) :
    Function.update (tapes data) .indexRestore value =
      tapes { data with indexRestore := value } := by
  funext stack
  cases stack <;> simp [tapes]

@[simp] theorem update_prefixCountdown (data : TapeData)
    (value : List Unit) :
    Function.update (tapes data) .prefixCountdown value =
      tapes { data with prefixCountdown := value } := by
  funext stack
  cases stack <;> simp [tapes]

@[simp] theorem update_rowReverse (data : TapeData) (value : List Token) :
    Function.update (tapes data) .rowReverse value =
      tapes { data with rowReverse := value } := by
  funext stack
  cases stack <;> simp [tapes]

@[simp] theorem update_rowForward (data : TapeData) (value : List Token) :
    Function.update (tapes data) .rowForward value =
      tapes { data with rowForward := value } := by
  funext stack
  cases stack <;> simp [tapes]

@[simp] theorem update_outputReverse (data : TapeData)
    (value : List Token) :
    Function.update (tapes data) .outputReverse value =
      tapes { data with outputReverse := value } := by
  funext stack
  cases stack <;> simp [tapes]

@[simp] theorem update_output (data : TapeData) (value : List Token) :
    Function.update (tapes data) .output value =
      tapes { data with output := value } := by
  funext stack
  cases stack <;> simp [tapes]

end RepresentativeEqualityRowsMachine
end LeanTrominoes
