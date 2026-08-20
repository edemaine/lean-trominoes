/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalAssembledRouteData
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMClauseOriginComputability
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMClauseCoreRouteComputability
import LeanTrominoes.PeriodicOrthocrossingConstructionComputability

/-! # Computability of translated clause incidence routes -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalClauseIncidenceRouteComputed_primrec :
    Primrec horizontalClauseIncidenceRouteComputed := by
  have origin : Primrec fun input : HorizontalClauseIncidenceRouteInput =>
      horizontalThreeDMClauseOriginComputed input.1.1.1 input.1.1.2 :=
    horizontalThreeDMClauseOriginComputed_primrec.comp
      (Primrec.fst.comp Primrec.fst)
  have route : Primrec fun input : HorizontalClauseIncidenceRouteInput =>
      PlanarThreeDM.X3CClauseOrthogonal.route input.1.2 input.2 :=
    x3cClauseOrthogonalRoute_primrec.comp
      (Primrec.pair
        (Primrec.snd.comp Primrec.fst) Primrec.snd)
  exact PeriodicOrthocrossing.translatePolyline_primrec.comp
    origin route

end PeriodicCNFStripReduction
end LeanTrominoes
