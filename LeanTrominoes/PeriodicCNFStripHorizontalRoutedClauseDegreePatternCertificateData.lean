/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DirectedClauseProfileCheck
import LeanTrominoes.PeriodicCNFFormulaShapeFinalExactOneData
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderClauseFrameData

/-! # Clause-degree pattern of finite routed headers -/

namespace LeanTrominoes.PeriodicCNFStripReduction
namespace HorizontalRoutedRouteHeaderClauseFrame

open PeriodicCNF
open PeriodicCNF.FormulaShapeDirectionOrdering
open PeriodicCNF.UnaryProgramClauseProfile
open PeriodicPlanarOneInThreeToThreeDM
open PlanarThreeDM

def routedClauseDegreeCheck (profile : DirectedClauseProfile) : Bool :=
  decide ((tokenClauseFans (.clause profile)).map ClauseRibbonFanData.hasRight =
    (FormulaShape.clauseProfiles
      (FormulaShapeFinalExactOne.shape
        (FormulaShapeDirectionOrdering.tokenBlock (.clause profile)))).map
          fun profile => decide (3 ≤ profile.literals.length)) &&
  decide ((tokenBlocks (.clause profile)).map List.length =
    (FormulaShape.clauseProfiles
      (FormulaShapeFinalExactOne.shape
        (FormulaShapeDirectionOrdering.tokenBlock (.clause profile)))).map
          fun profile => profile.literals.length)

end HorizontalRoutedRouteHeaderClauseFrame
end LeanTrominoes.PeriodicCNFStripReduction
