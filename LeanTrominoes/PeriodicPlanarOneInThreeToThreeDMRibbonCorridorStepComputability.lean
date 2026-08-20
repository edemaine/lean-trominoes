/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonCorridorSingletonStepComputability
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonCorridorNextStepComputability

noncomputable section

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

theorem ribbonCorridorCoreConsStep_primrec :
    Primrec ribbonCorridorCoreConsStep := by
  have tail : Primrec fun input : RibbonCorridorCoreConsInput =>
      input.2.2 :=
    Primrec.snd.comp Primrec.snd
  exact (Primrec.list_casesOn tail
    ribbonCorridorCoreSingletonStep_primrec
    ribbonCorridorCoreNextStep_primrec.to₂).of_eq fun input => by
      unfold ribbonCorridorCoreConsStep
      cases input.2.2 <;> rfl

theorem ribbonCorridorCoreStep_primrec :
    Primrec ribbonCorridorCoreStep := by
  have rest : Primrec fun input : RibbonCorridorCoreStepInput =>
      input.2.1 :=
    Primrec.fst.comp Primrec.snd
  exact (Primrec.list_casesOn rest (Primrec.const [])
    ribbonCorridorCoreConsStep_primrec.to₂).of_eq fun input => by
      unfold ribbonCorridorCoreStep
      cases input.2.1 <;> rfl

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
