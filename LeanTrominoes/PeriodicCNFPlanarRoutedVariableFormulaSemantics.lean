/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRoutedVariableGadgets

/-! # Semantics of one routed SAT variable gadget -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- Active-arm satisfaction is equivalent to the original total three-port
interface: inactive `getD` ports equal the center definitionally. -/
theorem routedVariableFormulaAt_holds_iff
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (assignment : PlanarSATNode Variable → Bool)
    (site : VariableRouteSite Variable) :
    FormulaHolds assignment
        (routedVariableFormulaAt formula site) ↔
      assignment (routedVariablePorts formula site).left =
          assignment (.atom site) ∧
        assignment (routedVariablePorts formula site).top =
          assignment (.atom site) ∧
        assignment (routedVariablePorts formula site).right =
          assignment (.atom site) := by
  unfold routedVariableFormulaAt routedVariableLinksAt routedVariablePorts
  exact equalityTakeThreeFamily_holds_iff
    (routedVariableNodes formula site) (.atom site)
    (fun node _ =>
      routedVariableEqualityPositions formula site
        node.duplicatorArm)
    assignment

end PeriodicOrthocrossing
end LeanTrominoes
