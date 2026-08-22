/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterTapes

/-! # Input-tape updates for source-occurrence route emission -/

namespace LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine

@[simp] theorem update_tapes_input (data : TapeData)
    (value : List InputSymbol) :
    Function.update (tapes data) .input value =
      tapes { data with input := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_occurrenceReverse (data : TapeData)
    (value : List OccurrenceToken) :
    Function.update (tapes data) .occurrenceReverse value =
      tapes { data with occurrenceReverse := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_occurrences (data : TapeData)
    (value : List OccurrenceToken) :
    Function.update (tapes data) .occurrences value =
      tapes { data with occurrences := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_targetReverse (data : TapeData)
    (value : List UnarySymbol) :
    Function.update (tapes data) .targetReverse value =
      tapes { data with targetReverse := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_targets (data : TapeData)
    (value : List UnarySymbol) :
    Function.update (tapes data) .targets value =
      tapes { data with targets := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

end LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine
