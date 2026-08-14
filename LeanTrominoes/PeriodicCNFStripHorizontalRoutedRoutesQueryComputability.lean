/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRoutesData

/-! # Generic routed-incidence query used by the concrete strip source -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq

/-- Query retained routed incidence data before composing with the guarded
source formula. -/
def horizontalRoutedRoutesQuery
    (input : (PeriodicCNF Variable × Nat) × Nat) : List Cell :=
  PeriodicOrthocrossing.retainedOrderedFixedEightPolarityNormalizedIncidenceRoutesComputed
    input.1.1 input.1.2 input.2

theorem horizontalRoutedRoutesQuery_primrec :
    Primrec horizontalRoutedRoutesQuery := by
  exact
    PeriodicOrthocrossing.retainedOrderedFixedEightPolarityNormalizedIncidenceRoutesComputed_primrec

end PeriodicCNFStripReduction
end LeanTrominoes
