/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalAssembledRouteData
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalOccurrenceVariableFanComputability
import LeanTrominoes.ThreeDM.Reduction.FromSAT.PeriodicPlanarOneInThreeToThreeDMVariableSiteTripleOfTypedComputability

/-! # Computability of variable incidence finite-table inputs -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalVariableIncidenceLocalRouteInputComputed_primrec :
    Primrec horizontalVariableIncidenceLocalRouteInputComputed := by
  exact Primrec.pair
    (horizontalOccurrenceVariableRibbonFanDataComputed_primrec.comp
      (Primrec.fst.comp Primrec.fst))
    (Primrec.pair
      (variableSiteTripleOfTyped_primrec.comp
        (Primrec.snd.comp Primrec.fst))
      Primrec.snd)

end PeriodicCNFStripReduction
end LeanTrominoes
