/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFBivariateTemplateEmitterMachine
import LeanTrominoes.PeriodicCNFUnaryProgramTokenAlgebra

/-!
# Token algebra for bivariate program ranges

The two-counter emitter uses its own recursive position range.  This file
identifies that range with the flat token stream of the corresponding
evaluated postorder programs, keeping the semantic bridge separate from the
larger machine and runtime proofs.
-/

namespace LeanTrominoes
namespace PeriodicCNF
namespace BivariateProgramTokenAlgebra

open UnaryProgramTokens
open UnaryProgramTokenAlgebra

/-- A bivariate recipe range is the flat stream of its per-position token
templates. -/
theorem positionRangeTokens_eq_flatMap
    (recipes : List BivariateProgramTemplates.Recipe)
    (first firstPosition count : Nat) :
    BivariateTemplateEmitterMachine.positionRangeTokens recipes first
        firstPosition count =
      (positions firstPosition count).flatMap fun position =>
        BivariateProgramTemplates.positionTokens recipes first position := by
  induction count generalizing firstPosition with
  | zero => rfl
  | succ count induction =>
      rw [BivariateTemplateEmitterMachine.positionRangeTokens_succ,
        positions_succ, List.flatMap_cons, induction]
      rfl

/-- For recipes obtained from a bivariate postorder program, the emitted
range is exactly the concatenation of the evaluated ordinary programs. -/
theorem positionRangeTokens_program
    (program : BivariateProgramTemplates.Program)
    (first firstPosition count : Nat) :
    BivariateTemplateEmitterMachine.positionRangeTokens program.recipes first
        firstPosition count =
      (positions firstPosition count).flatMap fun position =>
        ofProgram (program.evaluate first position) := by
  rw [positionRangeTokens_eq_flatMap]
  apply List.flatMap_congr
  intro position _
  exact BivariateProgramTemplates.Program.positionTokens_recipes
    program first position

end BivariateProgramTokenAlgebra
end PeriodicCNF
end LeanTrominoes
