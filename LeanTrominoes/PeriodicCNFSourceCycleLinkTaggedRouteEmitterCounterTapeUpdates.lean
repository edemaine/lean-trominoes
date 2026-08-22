/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterTapes

/-! # Counter-tape updates for tagged source cycle-link route emission -/

namespace LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine

@[simp] theorem update_tapes_clauseCount (data : TapeData)
    (value : List Unit) :
    Function.update (tapes data) .clauseCount value =
      tapes { data with clauseCount := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_literalCount (data : TapeData)
    (value : List Unit) :
    Function.update (tapes data) .literalCount value =
      tapes { data with literalCount := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_linkIndex (data : TapeData)
    (value : List Unit) :
    Function.update (tapes data) .linkIndex value =
      tapes { data with linkIndex := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_scratch (data : TapeData)
    (value : List Unit) :
    Function.update (tapes data) .scratch value =
      tapes { data with scratch := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

end LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine
