/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalRibbonSemanticData

/-! # Typed semantic horizontal planar presentation -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalRibbonInnerVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

/-- The final semantic ribbon presentation, exposed at the exact normalized
source and doubled placement used by proof-free occurrence routing. -/
def horizontalSemanticNormalizedPlanarPresentation
    (source : PeriodicCNF Nat) :
    (horizontalSemanticNormalizedRibbonSource source)
      |>.PlanarIncidencePresentation
        ((horizontalSemanticRoutedPlacement source).scale 2) :=
  horizontalSemanticNormalizedRibbonReadyPresentation source
    |>.toPlanarIncidencePresentation

end PeriodicCNFStripReduction
end LeanTrominoes
