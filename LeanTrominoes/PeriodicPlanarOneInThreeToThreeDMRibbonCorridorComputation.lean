/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonCorridorAssembly

/-! # A right-fold implementation of ribbon corridor assembly -/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget

abbrev RibbonCorridorCoreStepInput :=
  (WireColor × Cell) × (List Cell × List Cell)

abbrev RibbonCorridorCoreConsInput :=
  RibbonCorridorCoreStepInput × (Cell × List Cell)

abbrev RibbonCorridorCoreNextInput :=
  RibbonCorridorCoreConsInput × (Cell × List Cell)

abbrev RibbonCorridorCoreTileInput :=
  Cell × (Cell × (Cell × WireColor))

/-- The one-edge base route. -/
def ribbonCorridorCoreSingletonStep
    (input : RibbonCorridorCoreConsInput) : List Cell :=
  [ribbonMacrocellExit input.1.1.2
    (AxisDirection.between input.1.1.2 input.2.1)
    input.1.1.1]

/-- The local tile determined by three consecutive source points. -/
def ribbonCorridorCoreTileDirections
    (input : RibbonCorridorCoreTileInput) :
    AxisDirection × AxisDirection :=
  (AxisDirection.between input.1 input.2.1,
    AxisDirection.between input.2.1 input.2.2.1)

/-- Repack the three points as the macrocell route query. -/
def ribbonCorridorCoreTileRouteInput
    (input : RibbonCorridorCoreTileInput) :
    Cell × (AxisDirection × (AxisDirection × WireColor)) :=
  let directions := ribbonCorridorCoreTileDirections input
  (input.2.1, (directions.1, (directions.2, input.2.2.2)))

/-- The local tile determined by three consecutive source points. -/
def ribbonCorridorCoreTile
    (input : RibbonCorridorCoreTileInput) : List Cell :=
  let data := ribbonCorridorCoreTileRouteInput input
  ribbonMacrocellRoute data.1 data.2.1 data.2.2.1 data.2.2.2

/-- Join one computed local tile to the already-computed tail. -/
def ribbonCorridorCoreTileJoin
    (input : RibbonCorridorCoreTileInput × List Cell) : List Cell :=
  joinAtEndpoint (ribbonCorridorCoreTile input.1) input.2

/-- Repack the list-fold state for the local tile join. -/
def ribbonCorridorCoreNextStep
    (input : RibbonCorridorCoreNextInput) : List Cell :=
  ribbonCorridorCoreTileJoin
    ((input.1.1.1.2,
      (input.1.2.1, (input.2.1, input.1.1.1.1))),
      input.1.1.2.2)

/-- Inspect the tail after the second point. -/
def ribbonCorridorCoreConsStep
    (input : RibbonCorridorCoreConsInput) : List Cell :=
  match input.2.2 with
  | [] => ribbonCorridorCoreSingletonStep input
  | next :: tail =>
      ribbonCorridorCoreNextStep (input, (next, tail))

/-- One right-fold step, inspecting the already retained list tail. -/
def ribbonCorridorCoreStep
    (input : RibbonCorridorCoreStepInput) : List Cell :=
  match input.2.1 with
  | [] => []
  | second :: tail =>
      ribbonCorridorCoreConsStep (input, (second, tail))

/-- Proof-free right-fold implementation of the corridor core. -/
def ribbonCorridorCoreComputed
    (color : WireColor) (points : List Cell) : List Cell :=
  points.rec [] fun first rest recursive =>
    ribbonCorridorCoreStep
      ((color, first), (rest, recursive))

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
