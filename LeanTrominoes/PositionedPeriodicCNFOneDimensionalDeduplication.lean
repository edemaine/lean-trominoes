/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFOneDimensionalLists
import LeanTrominoes.PositionedPeriodicCNFDeduplication

/-!
# One-dimensional positioned-CNF deduplication

Removing positioned clauses with duplicate literal lists erases to ordinary
periodic-clause deduplication, which preserves zero vertical offsets.
-/

namespace LeanTrominoes
namespace PositionedPeriodicCNF

/-- Literal-list deduplication of a positioned periodic CNF preserves
one-dimensionality after positions are erased. -/
theorem deduplicateByLiterals_erase_isOneDimensional
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (horizontal : source.erase.IsOneDimensional) :
    source.deduplicateByLiterals.erase.IsOneDimensional := by
  rw [erase_deduplicateByLiterals]
  exact PeriodicCNF.IsOneDimensional.dedup horizontal

end PositionedPeriodicCNF
end LeanTrominoes
