/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeOfFormulaData
import LeanTrominoes.PeriodicCNFPlanarThreeSATThreePositioned

/-! # Formula-shape profiles of positioned formulas -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeOfFormula

/-- Erasing clause positions computes the canonical profile of each
positioned clause without changing clause order. -/
theorem profiles_erase {Variable : Type}
    (source : PositionedPeriodicCNF Variable) :
    profiles source.erase =
      source.clauses.map fun clause =>
        clauseProfile
          (ClauseProfileOccurrenceSplit.literalProfiles
            clause.literals) := by
  simp [profiles, PositionedPeriodicCNF.erase, List.map_map,
    Function.comp_def]

end FormulaShapeOfFormula
end PeriodicCNF
end LeanTrominoes
