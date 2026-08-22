/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeCrossoverDescriptorData

/-! # Pair presentation of fixed crossover descriptors -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeCrossoverDirection

/-- Thirteen consecutive two-token fields recover all twenty-six fixed
crossover descriptors in clause order. -/
theorem pairedDescriptors_eq_descriptors :
    pairedDescriptors = descriptors := by
  native_decide

end FormulaShapeCrossoverDirection
end PeriodicCNF
end LeanTrominoes
