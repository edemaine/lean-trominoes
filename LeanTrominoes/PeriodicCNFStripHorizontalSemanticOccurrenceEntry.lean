/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalNormalizedRibbonEraseBridge

/-! # Transported horizontal occurrence entries -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  horizontalRibbonInnerVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

/-- Regard an active entry of the executable normalized source as an active
entry of the equal semantic source. -/
def horizontalSemanticOccurrenceEntry
    (source : PeriodicCNF Nat) :
    ActiveOccurrenceEntry
        (horizontalNormalizedRoutedFormulaComputed source).erase →
      ActiveOccurrenceEntry
        (horizontalSemanticNormalizedRibbonSource source).erase :=
  Eq.mp
    (congrArg
      (fun formula : PeriodicCNF RoutedVariable =>
        ActiveOccurrenceEntry formula)
      (horizontalNormalizedRoutedEraseComputed_eq_semanticData source))

end PeriodicCNFStripReduction
end LeanTrominoes
