/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonCorridorComputation
import LeanTrominoes.PeriodicThreeDMNormalizationCompilerComputability

noncomputable section

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

theorem ribbonCorridorCoreTileDirections_primrec :
    Primrec ribbonCorridorCoreTileDirections := by
  let first : Primrec fun input : RibbonCorridorCoreTileInput =>
      input.1 :=
    Primrec.fst
  let second : Primrec fun input : RibbonCorridorCoreTileInput =>
      input.2.1 :=
    Primrec.fst.comp Primrec.snd
  let next : Primrec fun input : RibbonCorridorCoreTileInput =>
      input.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  exact Primrec.pair
    (PeriodicThreeDM.NormalizationCompiler.axisDirection_between_primrec.comp
      first second)
    (PeriodicThreeDM.NormalizationCompiler.axisDirection_between_primrec.comp
      second next)

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
