/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCrossoverFamily

/-! # Normalized clause blocks of the retained crossover family -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- The raw normalized crossover clauses, before any other retained family
is appended or any clause orbit is deduplicated. -/
def crossoverMetadataNormalizedClauses
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    List (PeriodicClause (WrappedPeriodicPlanarSATVariable Variable)) :=
  (drawingPlanarSATCrossoverClauseMetadata source.incidenceGraph).map
    (normalizedClause source)

/-- The canonical wrapped clause block named by one canonical crossing key. -/
def canonicalNormalizedCrossoverBlock
    {Variable : Type}
    (crossing : CrossingRecord) :
    List (PeriodicClause (WrappedPeriodicPlanarSATVariable Variable)) :=
  crossoverFormula.zipIdx.map fun taggedClause =>
    FormulaShapeCrossoverDirection.wrappedNormalizedClause
      crossing taggedClause.1

/-- The canonical wrapped clause block named by one physical halo crossing. -/
def normalizedCrossoverBlock
    {Variable : Type} [DecidableEq Variable]
    (graph : PeriodicGraph (CNFVertex Variable))
    (crossing : CrossingRecord) :
    List (PeriodicClause (WrappedPeriodicPlanarSATVariable Variable)) :=
  canonicalNormalizedCrossoverBlock
    (crossing.periodNormalize graph)

/-- Normalizing the metadata block at one physical crossing gives exactly
the canonical wrapped block at its period-normalized crossing. -/
theorem crossoverMetadataNormalizedClausesFor_eq
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (degree : source.incidenceGraph.DegreeAtMost 3)
    (isLocal : source.incidenceGraph.IsLocal)
    (crossing : CrossingRecord)
    (crossingMember : crossing ∈ orientedCrossingHalo source.incidenceGraph) :
    (drawingPlanarSATCrossoverClauseMetadataFor
        (Variable := Variable) crossing).map
        (normalizedClause source) =
      normalizedCrossoverBlock source.incidenceGraph crossing := by
  unfold drawingPlanarSATCrossoverClauseMetadataFor
    drawingPlanarSATCrossoverFormulaAt
    scopedCrossoverInstance instantiateFormula
    normalizedCrossoverBlock canonicalNormalizedCrossoverBlock
  simp only [List.map_map, List.zipIdx_map]
  apply List.map_congr_left
  intro taggedClause _taggedClauseMember
  exact normalizedClause_crossoverClauseAt_eq
    source wellFormed degree isLocal crossing crossingMember
    taggedClause.1 taggedClause.2

/-- The complete raw normalized crossover family is the flat map of its
canonical wrapped blocks over the actual physical halo enumeration. -/
theorem crossoverMetadataNormalizedClauses_eq_blocks
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (degree : source.incidenceGraph.DegreeAtMost 3)
    (isLocal : source.incidenceGraph.IsLocal) :
    crossoverMetadataNormalizedClauses source =
      (orientedCrossingHalo source.incidenceGraph).flatMap
        (normalizedCrossoverBlock source.incidenceGraph) := by
  unfold crossoverMetadataNormalizedClauses
    drawingPlanarSATCrossoverClauseMetadata
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro crossing crossingMember
  exact crossoverMetadataNormalizedClausesFor_eq
    source wellFormed degree isLocal crossing crossingMember

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
