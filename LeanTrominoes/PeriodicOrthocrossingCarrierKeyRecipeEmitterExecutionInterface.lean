/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterExecutionData

/-! # List-machine interface for carrier-key recipe-emitter execution -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyRecipeEmitterMachine

open Computability Turing
open RouteDescriptorPairCarrierKeyWordRecipes

theorem initList_eq_scanCfg (recipes : List Recipe)
    (input : List CarrierKeyRecipeEmitter.Token) :
    initList (machine recipes) input =
      scanCfg (initialState recipes.length) (initialData input) := by
  unfold initList machine scanCfg cfg initialData
  congr 1
  funext stack
  cases stack <;> simp [tapes]

theorem haltList_eq_haltDataCfg (recipes : List Recipe)
    (output : List DelimitedBinaryWords.Token) :
    haltList (machine recipes) output =
      haltDataCfg (initialState recipes.length)
        ⟨[], [], [], [], [], output⟩ := by
  unfold haltList machine haltDataCfg
  congr 1
  funext stack
  cases stack <;> simp [tapes]

end CarrierKeyRecipeEmitterMachine
end LeanTrominoes.PeriodicOrthocrossing
