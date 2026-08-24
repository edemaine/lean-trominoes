/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterTimePolynomial

/-! # Polynomial-time carrier-key recipe emission -/

namespace LeanTrominoes.PeriodicOrthocrossing

open Computability StateTransition Turing

namespace CarrierKeyRecipeEmitterMachine

open RouteDescriptorPairCarrierKeyWordRecipes

/-- For a fixed recipe list, compact carrier-key guarded-word emission is
linear-time in the compact input length. -/
noncomputable def computableInPolyTime (recipes : List Recipe) :
    @TM2ComputableInPolyTime
      (List CarrierKeyRecipeEmitter.Token)
      (List DelimitedBinaryWords.Token)
      CarrierKeyRecipeEmitter.Token DelimitedBinaryWords.Token id id
      (compiledTokens recipes) where
  tm := machine recipes
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := timePolynomial recipes
  outputsFun input := by
    have run := machine_outputsInTime recipes input
    have run' : TM2OutputsInTime (machine recipes)
        (List.map (Equiv.refl CarrierKeyRecipeEmitter.Token).invFun
          (id input))
        (some (List.map (Equiv.refl DelimitedBinaryWords.Token).invFun
          (id (compiledTokens recipes input))))
        (totalTime recipes input) := by
      simpa only [FiniteBlockTransducer.map_refl_invFun, id_eq] using run
    exact
      { toEvalsTo := run'.toEvalsTo
        steps_le_m := run'.steps_le_m.trans
          (totalTime_le_polynomial_eval recipes input) }

end CarrierKeyRecipeEmitterMachine
end LeanTrominoes.PeriodicOrthocrossing
