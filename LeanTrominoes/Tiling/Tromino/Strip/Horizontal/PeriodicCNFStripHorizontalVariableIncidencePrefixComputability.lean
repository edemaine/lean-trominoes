/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalAssembledRouteData
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalVariableIncidenceLocalRouteComputability
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalVariableIncidenceOriginComputability
import LeanTrominoes.Graphs.Drawings.Orthogonal.Construction.PeriodicOrthocrossingConstructionComputability

/-! # Computability of translated variable incidence prefixes -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalVariableIncidencePrefixComputed_primrec :
    Primrec horizontalVariableIncidencePrefixComputed := by
  exact PeriodicOrthocrossing.translatePolyline_primrec.comp
    horizontalVariableIncidenceOriginComputed_primrec
    horizontalVariableIncidenceLocalRouteComputed_primrec

end PeriodicCNFStripReduction
end LeanTrominoes
