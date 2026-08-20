/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonCorridorTileDirectionComputability
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonMacrocellComputability

noncomputable section

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

theorem ribbonCorridorCoreTileRouteInput_primrec :
    Primrec ribbonCorridorCoreTileRouteInput := by
  let second : Primrec fun input : RibbonCorridorCoreTileInput =>
      input.2.1 :=
    Primrec.fst.comp Primrec.snd
  let color : Primrec fun input : RibbonCorridorCoreTileInput =>
      input.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  exact Primrec.pair second
    (Primrec.pair
      (Primrec.fst.comp ribbonCorridorCoreTileDirections_primrec)
      (Primrec.pair
        (Primrec.snd.comp ribbonCorridorCoreTileDirections_primrec)
        color))

theorem ribbonCorridorCoreTile_primrec :
    Primrec ribbonCorridorCoreTile := by
  exact (ribbonMacrocellRoute_primrec.comp
    ribbonCorridorCoreTileRouteInput_primrec).of_eq fun _ => rfl

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
