/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalAssembledRouteData
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMVariableOriginComputability

/-! # Computability of variable incidence origins -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalVariableIncidenceOriginComputed_primrec :
    Primrec horizontalVariableIncidenceOriginComputed := by
  exact horizontalThreeDMVariableOriginComputed_primrec.comp
    (Primrec.fst.comp Primrec.fst)

end PeriodicCNFStripReduction
end LeanTrominoes
