/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
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

private theorem tokenClauseFans_hasRight_eq_finalClauseProfiles
    (token : FormulaShapeDirectionOrdering.Token) :
    (tokenClauseFans token).map ClauseRibbonFanData.hasRight =
      (FormulaShape.clauseProfiles
        (FormulaShapeFinalExactOne.shape
          (FormulaShapeDirectionOrdering.tokenBlock token))).map
            fun profile => decide (3 ≤ profile.literals.length) := by
  cases token with
  | «variable» => rfl
  | clause profile =>
      cases profile <;> native_decide +revert

private theorem tokenBlockLengths_eq_finalClauseProfileLengths
    (token : FormulaShapeDirectionOrdering.Token) :
    (tokenBlocks token).map List.length =
      (FormulaShape.clauseProfiles
        (FormulaShapeFinalExactOne.shape
          (FormulaShapeDirectionOrdering.tokenBlock token))).map
            fun profile => profile.literals.length := by
  cases token with
  | «variable» => rfl
  | clause profile =>
      cases profile <;> native_decide +revert

/-- The boundary-preserving routed-header blocks have exactly the clause
arities of the complete finite Figure 9, unit-elimination, and polarity
normalization profile transformation. -/
theorem outputBlockLengths_eq_finalClauseProfileLengths
    (source : List FormulaShapeDirectionOrdering.Token) :
    (outputBlocks source).map List.length =
      (FormulaShape.clauseProfiles
        (FormulaShapeFinalExactOne.shape
          (FormulaShapeDirectionOrdering.shape source))).map
            fun profile => profile.literals.length := by
  induction source with
  | nil => rfl
  | cons token source induction =>
      change
        (tokenBlocks token ++ outputBlocks source).map List.length = _
      rw [List.map_append,
        FormulaShapeDirectionOrdering.shape_cons]
      unfold FormulaShapeFinalExactOne.shape
      rw [List.flatMap_append, FormulaShape.clauseProfiles_append,
        List.map_append]
      exact congrArg₂ (fun first second => first ++ second)
        (tokenBlockLengths_eq_finalClauseProfileLengths token)
        induction

/-- A retained fan has a right terminal exactly when its corresponding final
clause profile is ternary. -/
theorem outputClauseFans_hasRight_eq_finalClauseProfiles
    (source : List FormulaShapeDirectionOrdering.Token) :
    (outputClauseFans source).map ClauseRibbonFanData.hasRight =
      (FormulaShape.clauseProfiles
        (FormulaShapeFinalExactOne.shape
          (FormulaShapeDirectionOrdering.shape source))).map
            fun profile => decide (3 ≤ profile.literals.length) := by
  induction source with
  | nil => rfl
  | cons token source induction =>
      have decomposition :
          outputClauseFans (token :: source) =
            tokenClauseFans token ++ outputClauseFans source := by
        simp [outputClauseFans, outputBlocks, tokenClauseFans]
      rw [decomposition, List.map_append,
        FormulaShapeDirectionOrdering.shape_cons]
      unfold FormulaShapeFinalExactOne.shape
      rw [List.flatMap_append, FormulaShape.clauseProfiles_append,
        List.map_append]
      exact congrArg₂ (fun first second => first ++ second)
        (tokenClauseFans_hasRight_eq_finalClauseProfiles token)
        induction

end HorizontalRoutedRouteHeaderClauseFrame
end LeanTrominoes.PeriodicCNFStripReduction
