/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFTrivariateTemplateEmitterExecutionData

/-! # List-machine interface for trivariate-emitter execution -/

namespace LeanTrominoes

open Computability Turing

namespace PeriodicCNF
namespace TrivariateTemplateEmitterMachine

open UnaryProgramTokens

theorem initList_eq_scanCfg {Data : Type} [Fintype Data] [Inhabited Data]
    (firstSelected secondSelected positionSelected : Data → Bool)
    (recipes : List Recipe) (ending : List Token)
    (workspace : List (Workspace Data)) :
    initList
        (machine Data firstSelected secondSelected positionSelected
          recipes ending)
        workspace =
      scanCfg (recipes := recipes) (initialData workspace) := by
  unfold initList machine scanCfg cfg initialData
  congr 1
  funext stack
  cases stack <;> simp [tapes]

theorem haltList_eq_haltCfg {Data : Type} [Fintype Data] [Inhabited Data]
    (firstSelected secondSelected positionSelected : Data → Bool)
    (recipes : List Recipe) (ending : List Token)
    (output : List (Workspace Data)) :
    haltList
        (machine Data firstSelected secondSelected positionSelected
          recipes ending)
        output =
      haltCfg (recipes := recipes) output := by
  unfold haltList machine haltCfg
  congr 1
  funext stack
  cases stack <;> simp [tapes]

@[simp] theorem haltDataCfg_empty_eq_haltCfg {Data : Type}
    {recipes : List Recipe} (output : List (Workspace Data)) :
    haltDataCfg (recipes := recipes)
        ⟨[], [], [], [], [], [], [], output⟩ =
      haltCfg (recipes := recipes) output :=
  rfl

end TrivariateTemplateEmitterMachine
end PeriodicCNF
end LeanTrominoes
