/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BoolSquareRowsMachine

/-! # Tape-update identities for the Boolean square-row machine -/

namespace LeanTrominoes
namespace BoolSquareRowsMachine

@[simp] theorem update_input (data : TapeData) (value : List Bool) :
    Function.update (tapes data) .input value =
      tapes { data with input := value } := by
  funext stack
  cases stack <;> simp [tapes]

@[simp] theorem update_sourceReverse (data : TapeData)
    (value : List Bool) :
    Function.update (tapes data) .sourceReverse value =
      tapes { data with sourceReverse := value } := by
  funext stack
  cases stack <;> simp [tapes]

@[simp] theorem update_work (data : TapeData) (value : List Unit) :
    Function.update (tapes data) .work value =
      tapes { data with work := value } := by
  funext stack
  cases stack <;> simp [tapes]

@[simp] theorem update_odd (data : TapeData) (value : List Unit) :
    Function.update (tapes data) .odd value =
      tapes { data with odd := value } := by
  funext stack
  cases stack <;> simp [tapes]

@[simp] theorem update_oddRestore (data : TapeData)
    (value : List Unit) :
    Function.update (tapes data) .oddRestore value =
      tapes { data with oddRestore := value } := by
  funext stack
  cases stack <;> simp [tapes]

@[simp] theorem update_root (data : TapeData) (value : List Unit) :
    Function.update (tapes data) .root value =
      tapes { data with root := value } := by
  funext stack
  cases stack <;> simp [tapes]

@[simp] theorem update_source (data : TapeData) (value : List Bool) :
    Function.update (tapes data) .source value =
      tapes { data with source := value } := by
  funext stack
  cases stack <;> simp [tapes]

@[simp] theorem update_rowCountdown (data : TapeData)
    (value : List Unit) :
    Function.update (tapes data) .rowCountdown value =
      tapes { data with rowCountdown := value } := by
  funext stack
  cases stack <;> simp [tapes]

@[simp] theorem update_rowRestore (data : TapeData)
    (value : List Unit) :
    Function.update (tapes data) .rowRestore value =
      tapes { data with rowRestore := value } := by
  funext stack
  cases stack <;> simp [tapes]

@[simp] theorem update_outputReverse (data : TapeData)
    (value : List OutputToken) :
    Function.update (tapes data) .outputReverse value =
      tapes { data with outputReverse := value } := by
  funext stack
  cases stack <;> simp [tapes]

@[simp] theorem update_output (data : TapeData)
    (value : List OutputToken) :
    Function.update (tapes data) .output value =
      tapes { data with output := value } := by
  funext stack
  cases stack <;> simp [tapes]

end BoolSquareRowsMachine
end LeanTrominoes
