/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeCrossoverDescriptorCandidateLookup
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataClauseDescriptorCandidateLookup

/-! # Representative descriptors of crossover clauses -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNF

open PeriodicOrthocrossing

namespace FormulaShapeRetainedPlanarMetadataDirection

/-- Public first-occurrence representative selection assigns every normalized
crossover clause its canonical fixed-gadget descriptor. -/
theorem representativeClauseDescriptor_eq_canonical_of_crossover_mem
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (degree : source.incidenceGraph.DegreeAtMost 3)
    (isLocal : source.incidenceGraph.IsLocal)
    (clause :
      PeriodicClause (WrappedPeriodicPlanarSATVariable Variable))
    (clauseMember :
      clause ∈ crossoverMetadataNormalizedClauses source) :
    representativeClauseDescriptor source clause =
      canonicalCrossoverClauseDescriptor clause := by
  have normalizedMember : clause ∈ normalizedClauses source := by
    rw [normalizedClauses_eq_crossover_append_nonCrossover source]
    exact List.mem_append_left _ clauseMember
  have clauseLookup :
      (normalizedClauses source)[
          (normalizedClauses source).idxOf clause]? = some clause :=
    List.getElem?_idxOf normalizedMember
  have candidateLookup :=
    metadataClauseDescriptorCandidates_getElem?_eq source clause
      ((normalizedClauses source).idxOf clause) clauseLookup
  have canonicalLookup :=
    metadataClauseDescriptorCandidates_idxOf_eq_canonical_of_crossover_mem
      source wellFormed degree isLocal clause clauseMember
  unfold representativeClauseDescriptor
  exact Option.some.inj (candidateLookup.symm.trans canonicalLookup)

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes

end
