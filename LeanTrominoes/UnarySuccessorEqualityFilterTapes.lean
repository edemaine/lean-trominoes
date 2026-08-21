/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnarySuccessorEqualityFilterMachine

/-! # Tape configurations for the unary successor-equality filter -/

namespace LeanTrominoes
namespace UnarySuccessorEqualityFilterMachine

open Turing

structure TapeData where
  input : List InputSymbol
  rankReverse : List UnarySymbol
  ranks : List UnarySymbol
  sizeReverse : List UnarySymbol
  sizes : List UnarySymbol
  candidate : List Unit
  outputReverse : List UnarySymbol
  output : List UnarySymbol

def tapes (data : TapeData) : ∀ stack, List (Alphabet stack)
  | .input => data.input
  | .rankReverse => data.rankReverse
  | .ranks => data.ranks
  | .sizeReverse => data.sizeReverse
  | .sizes => data.sizes
  | .candidate => data.candidate
  | .outputReverse => data.outputReverse
  | .output => data.output

def cfg (label : Label) (state : State) (data : TapeData) :
    TM2.Cfg Alphabet Label State :=
  ⟨some label, state, tapes data⟩

def emptyCfg (label : Label) (data : TapeData) :
    TM2.Cfg Alphabet Label State := cfg label .empty data

def haltCfg (output : List UnarySymbol) : TM2.Cfg Alphabet Label State :=
  ⟨none, .empty, tapes ⟨[], [], [], [], [], [], [], output⟩⟩

@[simp] theorem update_tapes_input (data : TapeData)
    (value : List InputSymbol) :
    Function.update (tapes data) .input value =
      tapes { data with input := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_rankReverse (data : TapeData)
    (value : List UnarySymbol) :
    Function.update (tapes data) .rankReverse value =
      tapes { data with rankReverse := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_ranks (data : TapeData)
    (value : List UnarySymbol) :
    Function.update (tapes data) .ranks value =
      tapes { data with ranks := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_sizeReverse (data : TapeData)
    (value : List UnarySymbol) :
    Function.update (tapes data) .sizeReverse value =
      tapes { data with sizeReverse := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_sizes (data : TapeData)
    (value : List UnarySymbol) :
    Function.update (tapes data) .sizes value =
      tapes { data with sizes := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_candidate (data : TapeData)
    (value : List Unit) :
    Function.update (tapes data) .candidate value =
      tapes { data with candidate := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_outputReverse (data : TapeData)
    (value : List UnarySymbol) :
    Function.update (tapes data) .outputReverse value =
      tapes { data with outputReverse := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_output (data : TapeData)
    (value : List UnarySymbol) :
    Function.update (tapes data) .output value =
      tapes { data with output := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

end UnarySuccessorEqualityFilterMachine
end LeanTrominoes
