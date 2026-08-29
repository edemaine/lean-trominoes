/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataTaggedCarrierTerminalData

/-! # Numeric coordinates of retained carrier terminal data -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

/-- The ordinary numeric coordinate underlying one classified terminal
datum. -/
def retainedTerminalDataCoordinate
    (terminal : RetainedTerminalData) : Nat × Nat :=
  (terminal.1.angularRank, terminal.2)

end PeriodicEightOccurrenceSplit
end LeanTrominoes
