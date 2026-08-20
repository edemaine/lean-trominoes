/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonCorridorComputation

/-! # Correctness of the proof-free ribbon corridor fold -/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget

@[simp] theorem ribbonCorridorCoreComputed_cons
    (color : WireColor) (first : Cell) (rest : List Cell) :
    ribbonCorridorCoreComputed color (first :: rest) =
      ribbonCorridorCoreStep
        ((color, first),
          (rest, ribbonCorridorCoreComputed color rest)) := by
  rfl

theorem ribbonCorridorCoreComputed_eq
    (color : WireColor) (points : List Cell) :
    ribbonCorridorCoreComputed color points =
      ribbonCorridorCore color points := by
  induction points with
  | nil =>
      simp [ribbonCorridorCoreComputed, ribbonCorridorCore]
  | cons first rest induction =>
      rw [ribbonCorridorCoreComputed_cons, induction]
      cases rest with
      | nil =>
          simp [ribbonCorridorCoreStep, ribbonCorridorCore]
      | cons second tail =>
          cases tail with
          | nil =>
              simp [ribbonCorridorCoreStep,
                ribbonCorridorCoreConsStep,
                ribbonCorridorCoreSingletonStep,
                ribbonCorridorCoreStart]
          | cons next tail =>
              cases tail with
              | nil =>
                  simp [ribbonCorridorCoreStep,
                    ribbonCorridorCoreConsStep,
                    ribbonCorridorCoreNextStep,
                    ribbonCorridorCoreTileJoin,
                    ribbonCorridorCoreTile,
                    ribbonCorridorCoreTileRouteInput,
                    ribbonCorridorCoreTileDirections,
                    ribbonCorridorCore, joinAtEndpoint]
              | cons fourth tail =>
                  simp [ribbonCorridorCoreStep,
                    ribbonCorridorCoreConsStep,
                    ribbonCorridorCoreNextStep,
                    ribbonCorridorCoreTileJoin,
                    ribbonCorridorCoreTile,
                    ribbonCorridorCoreTileRouteInput,
                    ribbonCorridorCoreTileDirections,
                    ribbonCorridorCore]

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
