/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListMapIdxOfPreimage
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataNonCrossoverNormalizedFamilyData

/-! # Raw metadata representatives within fallback families -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing

/-- The first carrier-metadata record normalizing to a retained carrier
clause is itself a carrier record. -/
theorem exists_carrierMetadata_lookup_of_normalized_mem
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (clause :
      PeriodicClause (WrappedPeriodicPlanarSATVariable Variable))
    (clauseMember : clause ∈ carrierMetadataNormalizedClauses source) :
    ∃ metadata : DrawingPlanarSATClauseMetadata Variable,
      (retainedDrawingPlanarSATCarrierClauseMetadata
          source.incidenceGraph)[
          (carrierMetadataNormalizedClauses source).idxOf clause]? =
        some metadata ∧
      ∃ link localClauseIndex,
        metadata.source = .carrier link localClauseIndex := by
  have mappedMember : clause ∈
      (retainedDrawingPlanarSATCarrierClauseMetadata
        source.incidenceGraph).map (normalizedClause source) := by
    exact clauseMember
  rcases IndexedListScan.exists_getElem?_idxOf_map
      (retainedDrawingPlanarSATCarrierClauseMetadata
        source.incidenceGraph)
      (normalizedClause source) clause mappedMember with
    ⟨metadata, metadataLookup, _normalizedEq, metadataMember⟩
  refine ⟨metadata, metadataLookup, ?_⟩
  unfold retainedDrawingPlanarSATCarrierClauseMetadata at metadataMember
  rcases List.mem_flatMap.mp metadataMember with
    ⟨link, _linkMember, metadataMember⟩
  unfold drawingPlanarSATCarrierClauseMetadataFor at metadataMember
  rcases List.mem_map.mp metadataMember with
    ⟨taggedClause, _taggedClauseMember, metadataEq⟩
  subst metadata
  exact ⟨link, taggedClause.2, rfl⟩

/-- The first bend-metadata record normalizing to a retained bend clause is
itself a bend record. -/
theorem exists_bendMetadata_lookup_of_normalized_mem
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (clause :
      PeriodicClause (WrappedPeriodicPlanarSATVariable Variable))
    (clauseMember : clause ∈ bendMetadataNormalizedClauses source) :
    ∃ metadata : DrawingPlanarSATClauseMetadata Variable,
      (drawingPlanarSATBendClauseMetadata source.incidenceGraph)[
          (bendMetadataNormalizedClauses source).idxOf clause]? =
        some metadata ∧
      ∃ routeBend localClauseIndex,
        metadata.source = .bend routeBend localClauseIndex := by
  have mappedMember : clause ∈
      (drawingPlanarSATBendClauseMetadata
        source.incidenceGraph).map (normalizedClause source) := by
    exact clauseMember
  rcases IndexedListScan.exists_getElem?_idxOf_map
      (drawingPlanarSATBendClauseMetadata source.incidenceGraph)
      (normalizedClause source) clause mappedMember with
    ⟨metadata, metadataLookup, _normalizedEq, metadataMember⟩
  refine ⟨metadata, metadataLookup, ?_⟩
  unfold drawingPlanarSATBendClauseMetadata at metadataMember
  rcases List.mem_flatMap.mp metadataMember with
    ⟨routeBend, _routeBendMember, metadataMember⟩
  unfold drawingPlanarSATBendClauseMetadataFor at metadataMember
  rcases List.mem_map.mp metadataMember with
    ⟨taggedClause, _taggedClauseMember, metadataEq⟩
  subst metadata
  exact ⟨routeBend, taggedClause.2, rfl⟩

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
