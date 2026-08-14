/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalProblemData

/-!
# Bridge from the direct horizontal problem view
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance] sourceVariableDecidableEq

/-- The direct problem view is definitionally the established concrete
problem. -/
theorem horizontalProblem_eq_problem (source : PeriodicCNF Nat) :
    horizontalProblem source = problem source := rfl

end PeriodicCNFStripReduction
end LeanTrominoes
