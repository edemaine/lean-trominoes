/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFixedEightSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeOfFormulaData

/-! # Transporting exact formula-shape contracts through fixed-eight -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeFixedEight

/-- The fixed-eight shape transformation preserves the named exact-shape
contract.  This small boundary keeps concrete downstream formulas opaque. -/
theorem correctFor
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (occurrencePorts : PeriodicEightOccurrenceSplit.OccurrencePorts)
    (sourceShape : List FormulaShape.Token)
    (sourceCorrect : FormulaShapeOfFormula.CorrectFor sourceShape source) :
    FormulaShapeOfFormula.CorrectFor
      (shape sourceShape)
      (PeriodicEightOccurrenceSplit.formula source occurrencePorts) := by
  unfold FormulaShapeOfFormula.CorrectFor at sourceCorrect ⊢
  exact shape_correct source occurrencePorts sourceShape
    sourceCorrect.1 sourceCorrect.2

end FormulaShapeFixedEight
end PeriodicCNF
end LeanTrominoes
