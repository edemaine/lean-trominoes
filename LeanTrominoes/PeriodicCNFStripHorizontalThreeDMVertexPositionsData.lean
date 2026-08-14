/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMTriplePositionData
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMRedPositionData
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMGreenPositionData
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMBluePositionData

/-! # Proof-free assembled vertex-position lists for the strip source -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalThreeDMTripleVariableDecidableEq

def horizontalThreeDMTriplePositionsData
    (source : PeriodicCNF Nat) : List Cell :=
  (PeriodicPlanarOneInThreeToThreeDM.triples
      (horizontalNormalizedRoutedFormulaComputed source).erase).map
    (PeriodicPlanarOneInThreeToThreeDM.assembledTriplePositionData
      (horizontalNormalizedRoutedFormulaComputed source).erase
      (horizontalThreeDMVariableOriginComputed source)
      (horizontalThreeDMClauseOriginComputed source))

def horizontalThreeDMRedPositionsData
    (source : PeriodicCNF Nat) : List Cell :=
  (PeriodicPlanarOneInThreeToThreeDM.redElements
      (horizontalNormalizedRoutedFormulaComputed source).erase).map
    (PeriodicPlanarOneInThreeToThreeDM.assembledRedElementPositionData
      (horizontalNormalizedRoutedFormulaComputed source).erase
      (horizontalThreeDMVariableOriginComputed source)
      (horizontalThreeDMClauseOriginComputed source))

def horizontalThreeDMGreenPositionsData
    (source : PeriodicCNF Nat) : List Cell :=
  (PeriodicPlanarOneInThreeToThreeDM.greenElements
      (horizontalNormalizedRoutedFormulaComputed source).erase).map
    (PeriodicPlanarOneInThreeToThreeDM.assembledGreenElementPositionData
      (horizontalNormalizedRoutedFormulaComputed source).erase
      (horizontalThreeDMVariableOriginComputed source)
      (horizontalThreeDMClauseOriginComputed source))

def horizontalThreeDMBluePositionsData
    (source : PeriodicCNF Nat) : List Cell :=
  (PeriodicPlanarOneInThreeToThreeDM.blueElements
      (horizontalNormalizedRoutedFormulaComputed source).erase).map
    (PeriodicPlanarOneInThreeToThreeDM.assembledBlueElementPositionData
      (horizontalNormalizedRoutedFormulaComputed source).erase
      (horizontalThreeDMVariableOriginComputed source)
      (horizontalThreeDMClauseOriginComputed source))

def horizontalThreeDMGreenBluePositionsData
    (source : PeriodicCNF Nat) : List Cell :=
  horizontalThreeDMGreenPositionsData source ++
    horizontalThreeDMBluePositionsData source

def horizontalThreeDMColoredPositionsData
    (source : PeriodicCNF Nat) : List Cell :=
  horizontalThreeDMRedPositionsData source ++
    horizontalThreeDMGreenBluePositionsData source

def horizontalThreeDMVertexPositionsData
    (source : PeriodicCNF Nat) : List Cell :=
  horizontalThreeDMTriplePositionsData source ++
    horizontalThreeDMColoredPositionsData source

end PeriodicCNFStripReduction
end LeanTrominoes
