/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierRepresentativeMetadataLookup
import LeanTrominoes.PeriodicThreeSATThreeCarrierClauseLookup

/-! # Exact final clause and metadata lookup for retained carriers -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing PlanarThreeSAT
open PeriodicThreeSATThree

local instance finalCarrierLookupThreeOccurrenceDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq (ThreeOccurrenceVariable Variable) :=
  fiveFamilyNormalizedThreeOccurrenceDecidableEq

/-- The global final-carrier index relation between a tagged semantic link
and its clause position after the crossover prefix. -/
structure finalCarrierTaggedLinkIndexed
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (taggedLink : EqualityLink CarrierNode × Bool)
    (clauseIndex : Nat) : Prop where
  member : (taggedLink, clauseIndex) ∈
    ((retainedDrawingCompleteCarrierLinks
        (PeriodicThreeSATThree.formula source).incidenceGraph).product
          [true, false]).zipIdx
      (crossoverMetadataNormalizedClausesDedup
        (PeriodicThreeSATThree.formula source)).length

/-- A tagged carrier implication at its global carrier-family index has both
the exact final normalized-clause lookup and the exact raw metadata lookup. -/
theorem finalCarrierClause_metadata_lookups
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceClausesNonempty : ∀ clause ∈ source.clauses, clause ≠ [])
    (positiveOffsets : ∀ incidence ∈ occurrenceIncidences source,
      incidence.edge.offset = (0, 0) ∨
        incidence.edge.offset = (1, 0))
    (taggedLink : EqualityLink CarrierNode × Bool)
    (clauseIndex : Nat)
    (taggedLinkIndexed :
      finalCarrierTaggedLinkIndexed source taggedLink clauseIndex) :
    let retained := PeriodicThreeSATThree.formula source
    let clause := normalizedCarrierClauseAt retained taggedLink
    let metadata := carrierClauseMetadataAt
      (Variable := ThreeOccurrenceVariable Variable)
        taggedLink.1 taggedLink.2
    (deduplicatedClauses retained)[clauseIndex]? = some clause ∧
      (retainedDrawingPlanarSATClauseMetadata retained)[
        (normalizedClauses retained).idxOf clause]? = some metadata := by
  let retained := PeriodicThreeSATThree.formula source
  let taggedLinks :=
    (retainedDrawingCompleteCarrierLinks
      retained.incidenceGraph).product [true, false]
  let clause := normalizedCarrierClauseAt retained taggedLink
  let metadata := carrierClauseMetadataAt
    (Variable := ThreeOccurrenceVariable Variable)
      taggedLink.1 taggedLink.2
  have taggedLinkIndexed := taggedLinkIndexed.member
  have taggedLinkMember : taggedLink ∈ taggedLinks :=
    List.fst_mem_of_mem_zipIdx taggedLinkIndexed
  have taggedClauseIndexed : (clause, clauseIndex) ∈
      (formulaCarrierMetadataNormalizedClauses source).zipIdx
        (crossoverMetadataNormalizedClausesDedup retained).length := by
    have mappedIndexed : (clause, clauseIndex) ∈
        (taggedLinks.map (normalizedCarrierClauseAt retained)).zipIdx
          (crossoverMetadataNormalizedClausesDedup retained).length := by
      rw [List.zipIdx_map]
      exact List.mem_map.mpr
        ⟨(taggedLink, clauseIndex), taggedLinkIndexed, rfl⟩
    simpa only [retained, taggedLinks, clause,
      formulaCarrierMetadataNormalizedClauses,
      carrierMetadataNormalizedClauses_eq_map_taggedLinks] using
        mappedIndexed
  have clauseLookup :
      (deduplicatedClauses retained)[clauseIndex]? = some clause := by
    simpa only [retained] using
      formulaCarrierMetadataNormalizedClauses_getElem?_of_mem_zipIdx
        source sourceLocal sourceWidth sourceClausesNonempty
          positiveOffsets (clause, clauseIndex) taggedClauseIndexed
  have retainedWellFormed : retained.incidenceGraph.IsWellFormed :=
    formula_incidenceGraph_isWellFormed source
  have retainedDegree : retained.incidenceGraph.DegreeAtMost 3 :=
    formula_incidenceGraph_degreeAtMostThree sourceWidth
  have retainedLocal : retained.incidenceGraph.IsLocal :=
    formula_incidenceGraph_isLocal sourceLocal
  have metadataLookup :
      (retainedDrawingPlanarSATClauseMetadata retained)[
          (normalizedClauses retained).idxOf clause]? = some metadata := by
    simpa only [metadata, clause] using
      carrierMetadata_global_lookup_of_normalized
        retained retainedWellFormed retainedDegree retainedLocal
          taggedLink taggedLinkMember
  exact ⟨clauseLookup, metadataLookup⟩

end PeriodicEightOccurrenceSplit
end LeanTrominoes
