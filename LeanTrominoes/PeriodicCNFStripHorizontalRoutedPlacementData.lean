/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedPolarityRoutedPlacementComputability
import LeanTrominoes.PeriodicCNFStripSourceFormulaComputability

/-! # Executable routed placement data for the concrete strip source -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

local instance horizontalRoutedPlacementSourceVariableDecidableEq :
    DecidableEq Variable :=
  Classical.decEq _

/-- Variables after the retained Figure 9 construction and routed polarity
normalization. -/
abbrev RoutedVariable :=
  PolarityNormalizedVariable
    (OneInThreeNoUnitVariable
      (PeriodicOrthocrossing.PeriodicPlanarOneInThreeThreeRawVariable
        Variable))

local instance horizontalRoutedPlacementVariableDecidableEq :
    DecidableEq RoutedVariable :=
  inferInstance

/-- Proof-free placement parallel to the concrete routed formula. -/
def horizontalRoutedPlacementComputed (source : PeriodicCNF Nat) :=
  PeriodicOrthocrossing.retainedOrderedFixedEightPolarityNormalizedPlacementComputed
    (sourceFormula source)

end PeriodicCNFStripReduction
end LeanTrominoes
