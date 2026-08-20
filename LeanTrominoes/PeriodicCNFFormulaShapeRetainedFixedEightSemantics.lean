/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFixedEightCorrectFor
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFixedEightData
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFixedEightInstances

/-! # Exact semantics of retained fixed-eight formula shapes -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedFixedEight

open ClauseProfileOccurrenceSplit
open PeriodicOrthocrossing
open UnaryProgramClauseProfile

/-- Any exact retained-planar shape becomes an exact shape of the actual
angular-port fixed-eight occurrence split.  The retained certificate supplies
the premise in a separate leaf. -/
theorem shape_correct_of_retained
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (occurrencePorts : PeriodicEightOccurrenceSplit.OccurrencePorts)
    (retainedCorrect :
      FormulaShapeOfFormula.CorrectFor
        (FormulaShapeRetainedPlanar.shape source)
        (retainedPlanarSATFormula source)) :
    @FormulaShapeOfFormula.CorrectFor
      (ThreeOccurrenceVariable
        (WrappedPeriodicPlanarSATVariable Variable))
      (@variableDecidableEq Variable inferInstance)
      (shape source)
      (PeriodicEightOccurrenceSplit.formula
        (retainedPlanarSATFormula source)
        occurrencePorts) := by
  letI wrappedDecidableEq :
      DecidableEq (WrappedPeriodicPlanarSATVariable Variable) :=
    @wrappedVariableDecidableEq Variable inferInstance
  exact FormulaShapeFixedEight.correctFor
    (retainedPlanarSATFormula source)
    occurrencePorts
    (FormulaShapeRetainedPlanar.shape source)
    retainedCorrect

end FormulaShapeRetainedFixedEight
end PeriodicCNF
end LeanTrominoes
