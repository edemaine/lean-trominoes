/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineFinalPolarityOperationListSemantics
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalClauseValueSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalColoredRoutedRequestBlockSemantics

/-! # Direct final Figure 9 polarity-operation semantics -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF
open PeriodicCNF.ClauseProfilePolarityRouteOperation
open PeriodicCNF.FormulaShapeFigureNineFinalClauseOrdering

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalPolarityOperationSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalPolarityOperationSemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

private theorem directSourceIsLocal
    (symbols : List encoding.Γ) :
    (directSourceFormula decider symbols).IsLocal := by
  simpa only [directSourceFormula] using
    sourceFormula_isLocal
      (PolySpaceCompiler.formulaOfSymbols decider symbols)

private theorem directSourceWidthAtMostThree
    (symbols : List encoding.Γ) :
    (directSourceFormula decider symbols).WidthAtMost 3 := by
  simpa only [directSourceFormula] using
    sourceFormula_widthAtMostThree
      (PolySpaceCompiler.formulaOfSymbols decider symbols)

private theorem directSourceOccurrencesAtMostThree
    (symbols : List encoding.Γ) :
    @PeriodicCNF.OccurrencesAtMost Variable instBEqOfDecidableEq
      (by infer_instance) 3 (directSourceFormula decider symbols) := by
  unfold directSourceFormula
  exact PeriodicCNF.occurrencesAtMost_congr_beq
    _ _ (by infer_instance) (by infer_instance) 3
    (sourceFormula (PolySpaceCompiler.formulaOfSymbols decider symbols))
    (sourceFormula_occurrencesAtMostThree
      (PolySpaceCompiler.formulaOfSymbols decider symbols))

private theorem directSourceClausesNonempty
    (symbols : List encoding.Γ) :
    ∀ clause ∈ (directSourceFormula decider symbols).clauses,
      clause ≠ [] := by
  simpa only [directSourceFormula] using
    sourceFormula_clausesNonempty
      (PolySpaceCompiler.formulaOfSymbols decider symbols)

/-- The direct header/tail pairs carry exactly the local literal index and
polarity operation of every literal in the actual retained final-clockwise
formula, in clause-major order. -/
theorem directFigureNinePolarityRoutePairs_map_indexedPolarity
    (symbols : List encoding.Γ) :
    (directFigureNinePolarityRoutePairs decider symbols).map
        (fun pair => pair.1.polarity.indexed) =
      ((PeriodicOrthocrossing.retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormula
          (directSourceFormula decider symbols)
          (directSourceIsLocal decider symbols)
          (directSourceWidthAtMostThree decider symbols)
          (directSourceOccurrencesAtMostThree decider symbols)
          (directSourceClausesNonempty decider symbols)).clauses.flatMap fun clause =>
            indexedDescriptors
              (clause.literals.map PeriodicLiteral.value)) := by
  unfold directFigureNinePolarityRoutePairs
  refine
    (PeriodicCNF.FormulaShapeFigureNineFinalClauseOrdering.sourcePairs_map_indexedPolarity
      _ _).trans ?_
  have valueEq :=
    PeriodicOrthocrossing.retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormula_clauseLiteralValues_eq_descriptors
        (directSourceFormula decider symbols)
        (directSourceIsLocal decider symbols)
        (directSourceWidthAtMostThree decider symbols)
        (directSourceOccurrencesAtMostThree decider symbols)
        (directSourceClausesNonempty decider symbols)
  simpa only [List.flatMap_map, Function.comp_apply] using
    congrArg (List.flatMap indexedDescriptors) valueEq.symm

end LeanTrominoes.PeriodicCNFStripReduction

end
