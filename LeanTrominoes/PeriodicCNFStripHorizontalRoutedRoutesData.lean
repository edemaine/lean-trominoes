/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedPolarityRoutedRoutesComputability
import LeanTrominoes.PeriodicCNFStripSourceFormulaComputability

/-! # Executable routed incidence data for the concrete strip source -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

local instance horizontalRoutedRoutesSourceVariableDecidableEq :
    DecidableEq Variable :=
  Classical.decEq _

/-- Proof-free routed incidence-route family for a concrete strip source. -/
def horizontalRoutedRoutesComputed (source : PeriodicCNF Nat) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  PeriodicOrthocrossing.retainedOrderedFixedEightPolarityNormalizedIncidenceRoutesComputed
    (sourceFormula source)

end PeriodicCNFStripReduction
end LeanTrominoes
