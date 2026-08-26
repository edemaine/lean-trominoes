/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFigureNineCycleDirectionData
import LeanTrominoes.PeriodicEightOccurrenceSplitExactVariableCount

/-! # Variable count of finite retained Figure 9 descriptors -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedFigureNineDirection

open PeriodicEightOccurrenceSplit
open PeriodicOrthocrossing
open PeriodicThreeSATThree

/-- The fixed-eight count is independent of the chosen decision procedure
for equality on occurrence copies. -/
private theorem formula_variableOccurrences_dedup_length'
    {Variable : Type} [DecidableEq Variable]
    [outputDecidableEq : DecidableEq (ThreeOccurrenceVariable Variable)]
    (source : PeriodicCNF Variable)
    (occurrencePorts : OccurrencePorts) :
    (PeriodicEightOccurrenceSplit.formula
        source occurrencePorts).variableOccurrences.dedup.length =
      FormulaShapeFixedEight.copiesPerVariable *
        source.variableOccurrences.dedup.length := by
  let structural : DecidableEq (ThreeOccurrenceVariable Variable) :=
    fun first second => instDecidableEqProd first second
  have outputDecidableEqEqual : outputDecidableEq = structural :=
    Subsingleton.elim _ _
  rw [outputDecidableEqEqual]
  exact PeriodicEightOccurrenceSplit.formula_variableOccurrences_dedup_length
    source occurrencePorts

/-- The actual final fixed-eight formula has nine distinct output variables
for every stable retained source variable used by the finite cycle stream. -/
theorem finalVariableCount_eq_copiesPerVariable_mul_sourceVariables
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
        source).erase.variableOccurrences.dedup.length =
      FormulaShapeFixedEight.copiesPerVariable *
        (sourceVariables
          (sourceScaledForFigureSeven source).erase).length := by
  rw [retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula_erase]
  unfold retainedDrawingEightOccurrenceSplitFormula
  rw [formula_variableOccurrences_dedup_length']
  apply congrArg (FormulaShapeFixedEight.copiesPerVariable * ·)
  rw [← sourceVariables_eq_variableOccurrences_dedup]
  simp [sourceScaledForFigureSeven, finalCoordinatedSource,
    retainedPlanarSATFormula]

end FormulaShapeRetainedFigureNineDirection
end PeriodicCNF
end LeanTrominoes
