/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFTrivariateTemplateEmitterTimePolynomial

/-! # Polynomial-time trivariate affine template emission -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace PeriodicCNF
namespace TrivariateTemplateEmitterMachine

/-- For fixed selectors, recipes, and ending, trivariate affine template
emission is polynomial-time in the complete retained workspace length. -/
noncomputable def computableInPolyTime {Data : Type} [Fintype Data]
    [Inhabited Data]
    (firstSelected secondSelected positionSelected : Data → Bool)
    (recipes : List Recipe) (ending : List UnaryProgramTokens.Token) :
    @TM2ComputableInPolyTime
      (List (Workspace Data)) (List (Workspace Data))
      (Workspace Data) (Workspace Data) id id
      (emittedOutput firstSelected secondSelected positionSelected recipes
        ending) where
  tm := machine Data firstSelected secondSelected positionSelected recipes ending
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := timePolynomial recipes ending
  outputsFun workspace := by
    have run := machine_outputsInTime firstSelected secondSelected
      positionSelected recipes ending workspace
    have run' : TM2OutputsInTime
        (machine Data firstSelected secondSelected positionSelected recipes
          ending)
        (List.map (Equiv.refl (Workspace Data)).invFun (id workspace))
        (some (List.map (Equiv.refl (Workspace Data)).invFun
          (id (emittedOutput firstSelected secondSelected positionSelected
            recipes ending workspace))))
        (totalTime firstSelected secondSelected positionSelected recipes ending
          workspace) := by
      simpa only [FiniteBlockTransducer.map_refl_invFun, id_eq] using run
    exact
      { toEvalsTo := run'.toEvalsTo
        steps_le_m := run'.steps_le_m.trans
          (totalTime_le_polynomial_eval firstSelected secondSelected
            positionSelected recipes ending workspace) }

end TrivariateTemplateEmitterMachine
end PeriodicCNF
end LeanTrominoes
