/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFigureNineDirectionExact
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFigureNineFiniteDirectionSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCanonicalElementDegreeCompiler
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedClauseDegreePattern

/-! # Direct final clause-degree shape -/

noncomputable section

set_option maxHeartbeats 800000

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF
open PeriodicCNF.FormulaShapeDirectionOrdering
open PeriodicCNF.FormulaShapeRetainedFigureNineDirection
open PeriodicCNF.UnaryProgramClauseProfile
open PeriodicPlanarOneInThreeToThreeDM
open PlanarThreeDM
open PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalClauseDegreePatternStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalClauseDegreePatternVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Boolean ternary-clause column represented by a finite directed source
shape after all three exact-one clause transformations. -/
def finalClauseProfileHasRights
    (source : List FormulaShapeDirectionOrdering.Token) : List Bool :=
  (FormulaShape.clauseProfiles
    (FormulaShapeFinalExactOne.shape
      (FormulaShapeDirectionOrdering.shape source))).map
        fun profile => decide (3 ≤ profile.literals.length)

private theorem finalClauseProfileHasRights_append_variableMarkers
    (source : List FormulaShapeDirectionOrdering.Token) (count : Nat) :
    finalClauseProfileHasRights
        (source ++ List.replicate count .variable) =
      finalClauseProfileHasRights source := by
  simp [finalClauseProfileHasRights,
    FormulaShapeDirectionOrdering.shape,
    FormulaShapeDirectionOrdering.tokenBlock,
    FormulaShapeFinalExactOne.shape,
    FormulaShapeFinalExactOne.tokenBlock,
    FormulaShape.clauseProfiles]

private theorem variableMarkers_cycleClauseBlocks
    {Atom : Type} (atoms : List Atom) :
    (List.replicate atoms.length
        FormulaShapeDirectionOrdering.Token.variable).flatMap
        directSourceFinalCycleClauseDescriptorBlock =
      atoms.flatMap fun _ =>
        FormulaShapeFixedEightDirection.cycleClauseDescriptors := by
  unfold directSourceFinalCycleClauseDescriptorBlock
  induction atoms with
  | nil => rfl
  | cons atom atoms induction =>
      simp [List.replicate_succ,
        FormulaShapeFixedEightDirection.cycleClauseBlock,
        induction]

/-- Removing the final distinct-variable marker suffix from the canonical
finite direction descriptor stream leaves exactly the direct parent-clause
descriptor stream. -/
theorem directSourceFinalClauseDescriptors_eq_finiteClausePrefix
    (symbols : List encoding.Γ) :
    directSourceFinalClauseDescriptors decider symbols =
      FormulaShapeRetainedFigureNineDirection.copiedClauseDescriptors
          (directSourceFormula decider symbols) ++
        FormulaShapeRetainedFigureNineDirection.finiteCycleClauseDescriptors
          (directSourceFormula decider symbols) := by
  unfold directSourceFinalClauseDescriptors
    directSourceFinalCycleClauseDescriptors
    directRetainedFigureNineCopiedClauseDescriptors
    FormulaShapeRetainedFigureNineDirection.finiteCycleClauseDescriptors
    directSourceFormula
  let atoms :=
    PeriodicThreeSATThree.sourceVariables
      (FormulaShapeRetainedFigureNineDirection.sourceScaledForFigureSeven
        (sourceFormula
          (PolySpaceCompiler.formulaOfSymbols decider symbols))).erase
  change
    FormulaShapeRetainedFigureNineDirection.copiedClauseDescriptors
          (sourceFormula
            (PolySpaceCompiler.formulaOfSymbols decider symbols)) ++
        (List.replicate atoms.length .variable).flatMap
          directSourceFinalCycleClauseDescriptorBlock =
      FormulaShapeRetainedFigureNineDirection.copiedClauseDescriptors
          (sourceFormula
            (PolySpaceCompiler.formulaOfSymbols decider symbols)) ++
        atoms.flatMap fun _ =>
          FormulaShapeFixedEightDirection.cycleClauseDescriptors
  exact congrArg
    (fun tail =>
      FormulaShapeRetainedFigureNineDirection.copiedClauseDescriptors
          (sourceFormula
            (PolySpaceCompiler.formulaOfSymbols decider symbols)) ++ tail)
    (variableMarkers_cycleClauseBlocks atoms)

/-- Direct clause fans retain exactly the binary/ternary pattern of the
canonical final exact-one formula shape. -/
theorem directSourceFinalClauseFans_hasRight_eq_finalShape
    (symbols : List encoding.Γ) :
    (directSourceFinalClauseFans decider symbols).map
        ClauseRibbonFanData.hasRight =
      (FormulaShape.clauseProfiles
        (FormulaShapeFinalExactOne.shape
          (FormulaShapeRetainedFigureNineSource.shape
            (directSourceFormula decider symbols)))).map
              fun profile => decide (3 ≤ profile.literals.length) := by
  let source := directSourceFormula decider symbols
  let clausePrefix :=
    FormulaShapeRetainedFigureNineDirection.copiedClauseDescriptors source ++
      FormulaShapeRetainedFigureNineDirection.finiteCycleClauseDescriptors
        source
  let variableCount :=
    (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
      source).erase.variableOccurrences.dedup.length
  have descriptorEq :
      directSourceFinalClauseDescriptors decider symbols = clausePrefix := by
    simpa only [source, clausePrefix] using
      directSourceFinalClauseDescriptors_eq_finiteClausePrefix
        decider symbols
  have finiteEq :
      FormulaShapeRetainedFigureNineDirection.finiteDescriptors source =
        clausePrefix ++ List.replicate variableCount .variable := by
    rfl
  have sourceLocal : source.IsLocal := by
    simpa only [source, directSourceFormula] using
      sourceFormula_isLocal
        (PolySpaceCompiler.formulaOfSymbols decider symbols)
  have sourceWidth : source.WidthAtMost 3 := by
    simpa only [source, directSourceFormula] using
      sourceFormula_widthAtMostThree
        (PolySpaceCompiler.formulaOfSymbols decider symbols)
  have sourceOccurrences :
      @PeriodicCNF.OccurrencesAtMost Variable instBEqOfDecidableEq
        (by infer_instance) 3 source := by
    unfold PeriodicCNF.OccurrencesAtMost
    intro atom
    exact
      (sourceFormula_occurrencesAtMostThree_canonicalBEq
        (PolySpaceCompiler.formulaOfSymbols decider symbols)) atom
  have sourceClausesNonempty : ∀ clause ∈ source.clauses, clause ≠ [] := by
    simpa only [source, directSourceFormula] using
      sourceFormula_clausesNonempty
        (PolySpaceCompiler.formulaOfSymbols decider symbols)
  calc
    (directSourceFinalClauseFans decider symbols).map
          ClauseRibbonFanData.hasRight =
        finalClauseProfileHasRights clausePrefix := by
      unfold directSourceFinalClauseFans
      rw [descriptorEq]
      exact
        HorizontalRoutedRouteHeaderClauseFrame.outputClauseFans_hasRight_eq_finalClauseProfiles
          clausePrefix
    _ = finalClauseProfileHasRights
          (FormulaShapeRetainedFigureNineDirection.finiteDescriptors
            source) := by
      rw [finiteEq,
        finalClauseProfileHasRights_append_variableMarkers]
    _ = finalClauseProfileHasRights
          (FormulaShapeRetainedFigureNineDirection.descriptors source) := by
      rw [FormulaShapeRetainedFigureNineDirection.descriptors_eq_finiteDescriptors
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty]
    _ =
        (FormulaShape.clauseProfiles
          (FormulaShapeFinalExactOne.shape
            (FormulaShapeRetainedFigureNineSource.shape source))).map
              fun profile => decide (3 ≤ profile.literals.length) := by
      unfold finalClauseProfileHasRights
      rw [show
          FormulaShapeDirectionOrdering.shape
              (FormulaShapeRetainedFigureNineDirection.descriptors source) =
            FormulaShapeRetainedFigureNineDirection.shape source by rfl]
      rw [FormulaShapeRetainedFigureNineDirection.shape_eq_sourceShape
        source sourceWidth sourceClausesNonempty]
    _ =
        (FormulaShape.clauseProfiles
          (FormulaShapeFinalExactOne.shape
            (FormulaShapeRetainedFigureNineSource.shape
              (directSourceFormula decider symbols)))).map
                fun profile => decide (3 ≤ profile.literals.length) := by
      rfl

end LeanTrominoes.PeriodicCNFStripReduction
