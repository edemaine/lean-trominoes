/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFRenamingData
import LeanTrominoes.PeriodicThreeCNFWidthThreeIdentity

/-! # Pointwise 3CNF lifting as formula renaming -/

namespace LeanTrominoes
namespace PeriodicThreeCNF

/-- The width-three literal lift is exactly injective atom renaming by
`Sum.inl`. -/
theorem liftFormula_eq_rename {Variable : Type*}
    (source : PeriodicCNF Variable) :
    liftFormula source =
      source.rename (Sum.inl : Variable → ThreeCNFVariable Variable) := by
  rfl

end PeriodicThreeCNF
end LeanTrominoes
