/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonCorridorComputation
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonMacrocellComputability

noncomputable section

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

theorem ribbonCorridorCoreSingletonStep_primrec :
    Primrec ribbonCorridorCoreSingletonStep := by
  let first : Primrec fun input : RibbonCorridorCoreConsInput =>
      input.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  let second : Primrec fun input : RibbonCorridorCoreConsInput =>
      input.2.1 :=
    Primrec.fst.comp Primrec.snd
  let color : Primrec fun input : RibbonCorridorCoreConsInput =>
      input.1.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  let direction : Primrec fun input : RibbonCorridorCoreConsInput =>
      AxisDirection.between input.1.1.2 input.2.1 :=
    PeriodicThreeDM.NormalizationCompiler.axisDirection_between_primrec.comp
      first second
  exact Primrec.list_cons.comp
    (ribbonMacrocellExit_primrec.comp
      (Primrec.pair first (Primrec.pair direction color)))
    (Primrec.const [])

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
