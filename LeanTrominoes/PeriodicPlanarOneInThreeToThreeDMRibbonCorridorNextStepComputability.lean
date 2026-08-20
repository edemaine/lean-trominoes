/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonCorridorTileComputability
import LeanTrominoes.PeriodicThreeDMNormalizationGeometryComputability

noncomputable section

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

theorem ribbonCorridorCoreTileJoin_primrec :
    Primrec ribbonCorridorCoreTileJoin := by
  exact
    (PeriodicThreeDM.NormalizationCompiler.joinAtEndpoint_primrec.comp
      (ribbonCorridorCoreTile_primrec.comp Primrec.fst)
      Primrec.snd).of_eq fun _ => rfl

theorem ribbonCorridorCoreNextStep_primrec :
    Primrec ribbonCorridorCoreNextStep := by
  have packed : Primrec fun input : RibbonCorridorCoreNextInput =>
      ((input.1.1.1.2,
        (input.1.2.1, (input.2.1, input.1.1.1.1))),
        input.1.1.2.2) :=
    Primrec.pair
      (Primrec.pair
        (Primrec.snd.comp (Primrec.fst.comp
          (Primrec.fst.comp Primrec.fst)))
        (Primrec.pair
          (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
          (Primrec.pair
            (Primrec.fst.comp Primrec.snd)
            (Primrec.fst.comp (Primrec.fst.comp
              (Primrec.fst.comp Primrec.fst))))))
      (Primrec.snd.comp (Primrec.snd.comp
        (Primrec.fst.comp Primrec.fst)))
  exact (ribbonCorridorCoreTileJoin_primrec.comp packed).of_eq fun _ => rfl

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
