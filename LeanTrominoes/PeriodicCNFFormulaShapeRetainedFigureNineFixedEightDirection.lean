/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFixedEightDirectionExact
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFigureNineDirectionData
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarDirectionData
import LeanTrominoes.PeriodicEightOccurrenceSplitExactVariableCount

/-! # Phase-major descriptors at the retained Figure 9 boundary -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedFigureNineDirection

open PeriodicOrthocrossing

/-- The fixed-eight count is independent of the chosen decision procedure
for equality on output occurrence copies. -/
private theorem formula_variableOccurrences_dedup_length'
    {Variable : Type} [DecidableEq Variable]
    [outputDecidableEq :
      DecidableEq (ThreeOccurrenceVariable Variable)]
    (source : PeriodicCNF Variable)
    (occurrencePorts : PeriodicEightOccurrenceSplit.OccurrencePorts) :
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

/-- The phase-major fixed-eight descriptor expansion has exactly the
distinct-variable count of the actual retained Figure 9 descriptor stream. -/
theorem variableCount_fixedEightDescriptors_eq
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    FormulaShape.variableCount
        (FormulaShapeDirectionOrdering.shape
          (FormulaShapeFixedEightDirection.descriptors
            (FormulaShapeRetainedPlanarDirection.descriptors source))) =
      FormulaShape.variableCount (shape source) := by
  rw [FormulaShapeFixedEightDirection.variableCount_shape_descriptors]
  rw [FormulaShapeDirectionOrdering.variableCount_shape]
  simp only [FormulaShapeRetainedPlanarDirection.descriptors,
    FormulaShapeDirectionOrdering.ofFormula]
  simp
  unfold shape descriptors
  rw [FormulaShapeDirectionOrdering.variableCount_shape]
  simp only [FormulaShapeDirectionOrdering.ofFormula]
  simp
  unfold retainedDrawingEightOccurrenceSplitFormula
    retainedPlanarSATFormula
  rw [formula_variableOccurrences_dedup_length']
  apply congrArg (FormulaShapeFixedEight.copiesPerVariable * ·)
  simp
  have wrappedDecidableEqEqual :
      (@drawingOrderedWrappedPeriodicPlanarSATVariableInstDecidableEq
          Variable _) =
        (@instDecidableEqWrappedPeriodicVariable
          (PeriodicPlanarSATVariable Variable)
          (@instDecidableEqPeriodicPlanarSATVariable Variable _)) :=
    Subsingleton.elim _ _
  rw [wrappedDecidableEqEqual]

end FormulaShapeRetainedFigureNineDirection
end PeriodicCNF
end LeanTrominoes
