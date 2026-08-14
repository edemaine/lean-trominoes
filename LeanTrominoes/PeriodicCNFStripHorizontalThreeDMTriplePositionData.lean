/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMClauseOriginData
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMVariableOriginComputability
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMGlobalPositionData

/-! # Executable assembled triple positions for the concrete strip source -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

local instance horizontalThreeDMTripleVariableDecidableEq :
    DecidableEq RoutedVariable :=
  Classical.decEq _

def horizontalThreeDMTriplePositionComputed
    (source : PeriodicCNF Nat)
    (triple :
      PeriodicPlanarOneInThreeToThreeDM.Triple RoutedVariable) : Cell :=
  PeriodicPlanarOneInThreeToThreeDM.assembledTriplePositionData
    (horizontalNormalizedRoutedFormulaComputed source).erase
    (horizontalThreeDMVariableOriginComputed source)
    (horizontalThreeDMClauseOriginComputed source)
    triple

end PeriodicCNFStripReduction
end LeanTrominoes
