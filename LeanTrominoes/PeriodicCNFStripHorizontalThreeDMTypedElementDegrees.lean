/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMVertexPositionAtData

/-! # Typed source behind computed horizontal 3DM element positions -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalThreeDMTripleVariableDecidableEq

/-- Typed exact-one source from which the computed numeric 3DM problem is
encoded. -/
def horizontalThreeDMTypedSourceComputed (source : PeriodicCNF Nat) :
    PeriodicCNF RoutedVariable :=
  (horizontalNormalizedRoutedFormulaComputed source).erase

def horizontalThreeDMRedElementsComputed (source : PeriodicCNF Nat) :=
  PeriodicPlanarOneInThreeToThreeDM.redElements
    (horizontalThreeDMTypedSourceComputed source)

def horizontalThreeDMGreenElementsComputed (source : PeriodicCNF Nat) :=
  PeriodicPlanarOneInThreeToThreeDM.greenElements
    (horizontalThreeDMTypedSourceComputed source)

def horizontalThreeDMBlueElementsComputed (source : PeriodicCNF Nat) :=
  PeriodicPlanarOneInThreeToThreeDM.blueElements
    (horizontalThreeDMTypedSourceComputed source)

end PeriodicCNFStripReduction
end LeanTrominoes
