/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalAssembledEdgeRouteData
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMEncodingComputability

/-! # Computability of the encoded horizontal 3DM problem -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalThreeDMProblemComputed_primrec :
    Primrec horizontalThreeDMProblemComputed := by
  exact PeriodicPlanarOneInThreeToThreeDM.encodedProblem_primrec.comp
    (PositionedPeriodicCNF.erase_primrec.comp
      horizontalNormalizedRoutedFormulaComputed_primrec)

end PeriodicCNFStripReduction
end LeanTrominoes
