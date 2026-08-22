/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListMapAppendIdxOfLookup
import LeanTrominoes.PeriodicCNFFormulaShapeCrossoverDescriptorPrefix
import LeanTrominoes.PeriodicCNFFormulaShapeCrossoverNormalizedPrefix

/-! # Lookup of canonical crossover descriptor candidates -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNF

open PeriodicOrthocrossing

namespace FormulaShapeRetainedPlanarMetadataDirection

/-- A normalized clause in the crossover prefix selects its canonical
descriptor at its first global normalized-clause occurrence. -/
theorem metadataClauseDescriptorCandidates_idxOf_eq_canonical_of_crossover_mem
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (degree : source.incidenceGraph.DegreeAtMost 3)
    (isLocal : source.incidenceGraph.IsLocal)
    (clause :
      PeriodicClause (WrappedPeriodicPlanarSATVariable Variable))
    (clauseMember :
      clause ∈ crossoverMetadataNormalizedClauses source) :
    (metadataClauseDescriptorCandidates source)[
        (normalizedClauses source).idxOf clause]? =
      some (canonicalCrossoverClauseDescriptor clause) := by
  have lookup :=
    IndexedListScan.map_append_getElem?_idxOf_append_of_mem
      (crossoverMetadataNormalizedClauses source)
      (nonCrossoverMetadataNormalizedClauses source)
      canonicalCrossoverClauseDescriptor
      (nonCrossoverMetadataClauseDescriptors source)
      clause clauseMember
  rw [← normalizedClauses_eq_crossover_append_nonCrossover source]
    at lookup
  rw [← metadataClauseDescriptorCandidates_eq_crossover_append_nonCrossover
    source wellFormed degree isLocal] at lookup
  exact lookup

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes

end
