/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataDirectionData

/-! # Duplicate freedom of retained normalized clauses -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

/-- The final normalized clause representatives contain no duplicates. -/
theorem deduplicatedClauses_nodup
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (deduplicatedClauses formula).Nodup := by
  unfold deduplicatedClauses
  exact List.nodup_dedup _

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
