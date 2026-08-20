/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFinalExactOneSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeOfFormulaData

/-! # Transporting exact formula shapes through final exact-one -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeFinalExactOne

local instance correctForOneInThreeVariableDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq (OneInThreeVariable Variable) := inferInstance

local instance correctForOneInThreeNoUnitVariableDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq (OneInThreeNoUnitVariable Variable) := inferInstance

local instance correctForPolarityNormalizedVariableDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq (PolarityNormalizedVariable Variable) := inferInstance

/-- Figure 9, unit elimination, and polarity normalization transport the
named exact-shape contract. -/
theorem correctFor
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceShape : List FormulaShape.Token)
    (sourceCorrect : FormulaShapeOfFormula.CorrectFor sourceShape source) :
    FormulaShapeOfFormula.CorrectFor
      (shape sourceShape)
      (PeriodicOneInThreePolarityNormalization.formula
        (PeriodicOneInThreeNoUnits.formula
          (PeriodicOneInThree.formula source))) := by
  unfold FormulaShapeOfFormula.CorrectFor at sourceCorrect ⊢
  exact shape_correct source sourceShape sourceCorrect.1 sourceCorrect.2

end FormulaShapeFinalExactOne
end PeriodicCNF
end LeanTrominoes
