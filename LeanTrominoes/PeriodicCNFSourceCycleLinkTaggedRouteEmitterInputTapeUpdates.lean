/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterTapes

/-! # Input-tape updates for tagged source cycle-link route emission -/

namespace LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine

@[simp] theorem update_tapes_input (data : TapeData)
    (value : List InputSymbol) :
    Function.update (tapes data) .input value =
      tapes { data with input := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_tagReverse (data : TapeData)
    (value : List Tag) :
    Function.update (tapes data) .tagReverse value =
      tapes { data with tagReverse := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_tags (data : TapeData) (value : List Tag) :
    Function.update (tapes data) .tags value =
      tapes { data with tags := value } := by
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

end LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine
