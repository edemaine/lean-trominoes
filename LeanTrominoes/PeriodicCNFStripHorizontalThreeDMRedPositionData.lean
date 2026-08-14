/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMTriplePositionData

/-! # Executable assembled red-element positions for the strip source -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalThreeDMTripleVariableDecidableEq

def horizontalThreeDMRedPositionComputed
    (source : PeriodicCNF Nat)
    (element :
      PeriodicPlanarOneInThreeToThreeDM.RedElement RoutedVariable) : Cell :=
  PeriodicPlanarOneInThreeToThreeDM.assembledRedElementPositionData
    (horizontalNormalizedRoutedFormulaComputed source).erase
    (horizontalThreeDMVariableOriginComputed source)
    (horizontalThreeDMClauseOriginComputed source)
    element

end PeriodicCNFStripReduction
end LeanTrominoes
