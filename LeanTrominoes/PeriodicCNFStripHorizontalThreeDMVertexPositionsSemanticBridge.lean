/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMVertexPositionsAssembledBridge
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMOriginSemanticBridge
import LeanTrominoes.PeriodicCNFStripHorizontalNormalizedRibbonEraseBridge

/-! # Semantic bridge for the complete horizontal vertex-position list -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalThreeDMVertexPositionsComputed_eq_semantic
    (source : PeriodicCNF Nat)
    (width :
      (horizontalSemanticNormalizedRibbonSource source).erase.WidthAtMost 3)
    (compatible : SourceRibbonFansClockwiseCompatible
      ((horizontalSemanticNormalizedRibbonReadyPresentation source)
        |>.toPlanarIncidencePresentation)) :
    horizontalThreeDMVertexPositionsComputed source =
      @assembledVertexPositions
        RoutedVariable horizontalRibbonRoutedVariableDecidableEq
        (horizontalSemanticNormalizedRibbonSource source).erase
        (coordinatedSourceRibbonThreeStrandRouting
          (horizontalSemanticNormalizedRibbonReadyPresentation source)
          width compatible) := by
  rw [horizontalThreeDMVertexPositionsComputed_eq_assembled]
  have decidableEqCoherence :
      horizontalThreeDMTripleVariableDecidableEq =
        horizontalRibbonRoutedVariableDecidableEq :=
    Subsingleton.elim _ _
  have positionsCoherence :
      @assembledVertexPositionsData RoutedVariable
          horizontalThreeDMTripleVariableDecidableEq
          (horizontalNormalizedRoutedFormulaComputed source).erase
          (horizontalThreeDMVariableOriginComputed source)
          (horizontalThreeDMClauseOriginComputed source) =
        @assembledVertexPositionsData RoutedVariable
          horizontalRibbonRoutedVariableDecidableEq
          (horizontalNormalizedRoutedFormulaComputed source).erase
          (horizontalThreeDMVariableOriginComputed source)
          (horizontalThreeDMClauseOriginComputed source) :=
    congrArg
      (fun decEq : DecidableEq RoutedVariable =>
        @assembledVertexPositionsData RoutedVariable decEq
          (horizontalNormalizedRoutedFormulaComputed source).erase
          (horizontalThreeDMVariableOriginComputed source)
          (horizontalThreeDMClauseOriginComputed source))
      decidableEqCoherence
  rw [positionsCoherence]
  rw [horizontalNormalizedRoutedEraseComputed_eq_semanticData]
  let routing := coordinatedSourceRibbonThreeStrandRouting
    (horizontalSemanticNormalizedRibbonReadyPresentation source)
    width compatible
  have variableOrigin : horizontalThreeDMVariableOriginComputed source =
      routing.variableOrigin := by
    funext atom
    exact horizontalThreeDMVariableOriginComputed_eq_routing
      source width compatible atom
  have clauseOrigin : horizontalThreeDMClauseOriginComputed source =
      routing.clauseOrigin := by
    funext clauseIndex
    exact horizontalThreeDMClauseOriginComputed_eq_routing
      source width compatible clauseIndex
  rw [variableOrigin, clauseOrigin]
  exact assembledVertexPositionsData_eq_routing routing

end PeriodicCNFStripReduction
end LeanTrominoes
