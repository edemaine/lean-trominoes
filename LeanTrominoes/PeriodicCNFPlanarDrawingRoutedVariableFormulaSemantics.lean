/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRoutedVariableFormulaSemantics

/-! # Semantics of the routed SAT variable-gadget family -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- The variable family holds exactly when all three (possibly padded) route
ports agree with the central lifted atom at every represented site. -/
theorem drawingRoutedVariableFormula_holds_iff
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (assignment : PlanarSATNode Variable → Bool) :
    FormulaHolds assignment (drawingRoutedVariableFormula formula) ↔
      ∀ site ∈ drawingVariableRouteSites formula,
        assignment (routedVariablePorts formula site).left =
            assignment (.atom site) ∧
          assignment (routedVariablePorts formula site).top =
            assignment (.atom site) ∧
          assignment (routedVariablePorts formula site).right =
            assignment (.atom site) := by
  rw [drawingRoutedVariableFormula, formulaHolds_flatMap_iff]
  constructor
  · intro holds site siteMem
    exact
      (routedVariableFormulaAt_holds_iff
        formula assignment site).mp
        (holds site siteMem)
  · intro holds site siteMem
    exact
      (routedVariableFormulaAt_holds_iff
        formula assignment site).mpr
        (holds site siteMem)

end PeriodicOrthocrossing
end LeanTrominoes
