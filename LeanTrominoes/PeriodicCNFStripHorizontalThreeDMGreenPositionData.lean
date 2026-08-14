/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMTriplePositionData

/-! # Executable assembled green-element positions for the strip source -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalThreeDMTripleVariableDecidableEq

def horizontalThreeDMGreenPositionComputed
    (source : PeriodicCNF Nat)
    (element :
      PeriodicPlanarOneInThreeToThreeDM.GreenElement RoutedVariable) : Cell :=
  PeriodicPlanarOneInThreeToThreeDM.assembledGreenElementPositionData
    (horizontalNormalizedRoutedFormulaComputed source).erase
    (horizontalThreeDMVariableOriginComputed source)
    (horizontalThreeDMClauseOriginComputed source)
    element

end PeriodicCNFStripReduction
end LeanTrominoes
