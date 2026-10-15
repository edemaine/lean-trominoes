/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalRoutedClauseDegreePatternCertificates.Case0
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalRoutedClauseDegreePatternCertificates.Case1
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalRoutedClauseDegreePatternCertificates.Case2
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalRoutedClauseDegreePatternCertificates.Case3
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalRoutedClauseDegreePatternCertificates.Case4
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalRoutedClauseDegreePatternCertificates.Case5
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalRoutedClauseDegreePatternCertificates.Case6
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalRoutedClauseDegreePatternCertificates.Case7
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalRoutedClauseDegreePatternCertificates.Case8
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalRoutedClauseDegreePatternCertificates.Case9
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalRoutedClauseDegreePatternCertificates.Case10
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalRoutedClauseDegreePatternCertificates.Case11
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalRoutedClauseDegreePatternCertificates.Case12
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalRoutedClauseDegreePatternCertificates.Case13
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalRoutedClauseDegreePatternCertificates.Case14
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalRoutedClauseDegreePatternCertificates.Case15
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalRoutedClauseDegreePatternCertificates.Case16
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalRoutedClauseDegreePatternCertificates.Case17
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalRoutedClauseDegreePatternCertificates.Case18
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalRoutedClauseDegreePatternCertificates.Case19

/-! # Clause-degree pattern of finite routed headers -/

namespace LeanTrominoes.PeriodicCNFStripReduction
namespace HorizontalRoutedRouteHeaderClauseFrame

open PeriodicCNF
open PeriodicCNF.FormulaShapeDirectionOrdering
open PeriodicCNF.UnaryProgramClauseProfile
open PeriodicPlanarOneInThreeToThreeDM
open PlanarThreeDM

private theorem routedClauseDegreeCheck_first_correct
    (first : LeanTrominoes.PeriodicCNF.UnaryProgramClauseProfile.LiteralProfile)
    (direction : AxisDirection) : firstDirectedProfileCheck routedClauseDegreeCheck first direction = true := by
  rcases first with ⟨nextSlice, value⟩
  cases nextSlice <;> cases value <;> cases direction
  · exact routedClauseDegreeCheck_case0
  · exact routedClauseDegreeCheck_case1
  · exact routedClauseDegreeCheck_case2
  · exact routedClauseDegreeCheck_case3
  · exact routedClauseDegreeCheck_case4
  · exact routedClauseDegreeCheck_case5
  · exact routedClauseDegreeCheck_case6
  · exact routedClauseDegreeCheck_case7
  · exact routedClauseDegreeCheck_case8
  · exact routedClauseDegreeCheck_case9
  · exact routedClauseDegreeCheck_case10
  · exact routedClauseDegreeCheck_case11
  · exact routedClauseDegreeCheck_case12
  · exact routedClauseDegreeCheck_case13
  · exact routedClauseDegreeCheck_case14
  · exact routedClauseDegreeCheck_case15
  · exact routedClauseDegreeCheck_case16
  · exact routedClauseDegreeCheck_case17
  · exact routedClauseDegreeCheck_case18
  · exact routedClauseDegreeCheck_case19

private theorem routedClauseDegreeCheck_correct (profile : DirectedClauseProfile) :
    routedClauseDegreeCheck profile = true :=
  firstDirectedProfileCheck_sound routedClauseDegreeCheck routedClauseDegreeCheck_first_correct profile

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
      have checked := routedClauseDegreeCheck_correct profile
      simp only [routedClauseDegreeCheck, Bool.and_eq_true, decide_eq_true_eq] at checked
      exact checked.1

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
      have checked := routedClauseDegreeCheck_correct profile
      simp only [routedClauseDegreeCheck, Bool.and_eq_true, decide_eq_true_eq] at checked
      exact checked.2

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
