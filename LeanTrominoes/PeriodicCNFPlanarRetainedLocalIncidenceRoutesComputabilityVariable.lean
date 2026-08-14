/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedLocalIncidenceRoutesComputabilityVariableTransform

/-! # Primitive-recursive retained variable routes -/

noncomputable section

namespace LeanTrominoes

open PlanarThreeSAT

set_option maxHeartbeats 1000000

namespace PeriodicOrthocrossing

def routedVariableRoute
    {Variable : Type*} [DecidableEq Variable]
    (input : RoutedVariableRouteInput Variable) : List Cell :=
  ((duplicatorArmStraightIncidenceDrawing
    input.1.1.2).routes input.1.2 input.2).map
      (Cell.add
        (routedVariableOrigin input.1.1.1.1 input.1.1.1.2))

theorem routedVariableRoute_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    @Primrec (RoutedVariableRouteInput Variable) (List Cell)
      inferInstance inferInstance
      (routedVariableRoute (Variable := Variable)) := by
  exact Primrec.list_map
    PlanarThreeSAT.duplicatorArmStraightVariableInput_primrec
    routedVariableRouteTransform_primrec.to₂




end PeriodicOrthocrossing
end LeanTrominoes
