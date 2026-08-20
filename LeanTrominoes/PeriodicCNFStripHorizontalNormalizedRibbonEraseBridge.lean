/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalNormalizedRibbonSourceBridge

/-! # Erased normalized horizontal ribbon source -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

/-- The executable and semantic normalized ribbon sources have the same
unlabelled incidence formula. -/
theorem horizontalNormalizedRoutedEraseComputed_eq_semanticData
    (source : PeriodicCNF Nat) :
    (horizontalNormalizedRoutedFormulaComputed source).erase =
      (horizontalSemanticNormalizedRibbonSource source).erase :=
  congrArg PositionedPeriodicCNF.erase
    (horizontalNormalizedRoutedFormulaComputed_eq_semanticData source)

end PeriodicCNFStripReduction
end LeanTrominoes
