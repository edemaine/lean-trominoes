/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeCrossoverInternalClassifierBlock

/-! # Internal atoms in the normalized crossover family -/

namespace LeanTrominoes
namespace PeriodicCNF

open PeriodicOrthocrossing

namespace FormulaShapeRetainedPlanarMetadataDirection

/-- Every clause in the raw normalized crossover family contains a
crossover-internal atom. -/
theorem crossoverMetadataNormalizedClause_hasCrossoverInternal
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (degree : source.incidenceGraph.DegreeAtMost 3)
    (isLocal : source.incidenceGraph.IsLocal)
    (clause :
      PeriodicClause (WrappedPeriodicPlanarSATVariable Variable))
    (clauseMember :
      clause ∈ crossoverMetadataNormalizedClauses source) :
    normalizedClauseHasCrossoverInternal clause = true := by
  rw [crossoverMetadataNormalizedClauses_eq_blocks
    source wellFormed degree isLocal] at clauseMember
  rcases List.mem_flatMap.mp clauseMember with
    ⟨crossing, _crossingMember, blockMember⟩
  unfold normalizedCrossoverBlock at blockMember
  exact canonicalNormalizedCrossoverBlock_hasCrossoverInternal_of_mem
    (crossing.periodNormalize source.incidenceGraph)
    clause blockMember

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
