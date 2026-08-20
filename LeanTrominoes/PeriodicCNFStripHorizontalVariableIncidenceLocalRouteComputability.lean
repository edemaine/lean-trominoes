/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalVariableIncidencePrefixInputComputability
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMVariableSiteRouteComputability

/-! # Computability of finite variable incidence routes -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalVariableIncidenceLocalRouteComputed_primrec :
    Primrec horizontalVariableIncidenceLocalRouteComputed := by
  exact variableSiteRouteData_primrec.comp
    horizontalVariableIncidenceLocalRouteInputComputed_primrec

end PeriodicCNFStripReduction
end LeanTrominoes
