/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeCarrierClauseLookup
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataNormalizedCarrierRepresentativeDescriptors
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseQueryFallbackListSemantics
import LeanTrominoes.RetainedAngularFanFinalCarrierMetadataSemantics
import LeanTrominoes.RetainedAngularFanFinalDirectSourceChoiceFallback

/-! # Exact final copied-query semantics for retained carriers -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

local instance finalCarrierQueryThreeOccurrenceDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq (ThreeOccurrenceVariable Variable) :=
  PeriodicThreeSATThree.fiveFamilyNormalizedThreeOccurrenceDecidableEq

/-- The exact final queries occupying the retained-carrier subfamily evaluate
to the established carrier metadata descriptor stream. -/
theorem retainedFinalCarrierClauseQueryDescriptors_formula_eq
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceClausesNonempty : ∀ clause ∈ source.clauses, clause ≠ [])
    (positiveOffsets : ∀ incidence ∈
      PeriodicThreeSATThree.occurrenceIncidences source,
      incidence.edge.offset = (0, 0) ∨
        incidence.edge.offset = (1, 0)) :
    let formula := PeriodicThreeSATThree.formula source
    let crossoverClauses :=
      crossoverMetadataNormalizedClausesDedup formula
    let carrierClauses :=
      PeriodicThreeSATThree.formulaCarrierMetadataNormalizedClauses source
    retainedFinalCopiedClauseDescriptors
        (retainedFinalIndexedClauseQueriesFrom formula
          crossoverClauses.length carrierClauses) =
      carrierMetadataClauseDescriptors formula := by
  dsimp only
  let formula := PeriodicThreeSATThree.formula source
  let crossoverClauses :=
    crossoverMetadataNormalizedClausesDedup formula
  let carrierClauses :=
    PeriodicThreeSATThree.formulaCarrierMetadataNormalizedClauses source
  have formulaWellFormed : formula.incidenceGraph.IsWellFormed :=
    PeriodicThreeSATThree.formula_incidenceGraph_isWellFormed source
  have formulaDegree : formula.incidenceGraph.DegreeAtMost 3 :=
    PeriodicThreeSATThree.formula_incidenceGraph_degreeAtMostThree
      sourceWidth
  have formulaLocal : formula.incidenceGraph.IsLocal :=
    PeriodicThreeSATThree.formula_incidenceGraph_isLocal sourceLocal
  have clauseLookups :
      ∀ taggedClause ∈ carrierClauses.zipIdx crossoverClauses.length,
        (deduplicatedClauses formula)[taggedClause.2]? =
          some taggedClause.1 := by
    intro taggedClause taggedClauseMember
    simpa only [formula, crossoverClauses, carrierClauses] using
      PeriodicThreeSATThree.formulaCarrierMetadataNormalizedClauses_getElem?_of_mem_zipIdx
        source sourceLocal sourceWidth sourceClausesNonempty
          positiveOffsets taggedClause taggedClauseMember
  have choicesNone :
      ∀ taggedClause ∈ carrierClauses.zipIdx crossoverClauses.length,
        ∀ taggedLiteral ∈ taggedClause.1.zipIdx,
          retainedFinalDirectSourceRouteChoice?
              formula taggedClause.2 taggedLiteral.2 = none := by
    intro taggedClause taggedClauseMember taggedLiteral _taggedLiteralMember
    have clauseLookup := clauseLookups taggedClause taggedClauseMember
    have carrierMember :
        taggedClause.1 ∈ carrierMetadataNormalizedClauses formula := by
      exact List.fst_mem_of_mem_zipIdx taggedClauseMember
    rcases
        exists_finalCarrierMetadata_of_clause_lookup
          formula formulaWellFormed formulaDegree formulaLocal
          taggedClause.2 taggedClause.1 clauseLookup carrierMember with
      ⟨metadata, finalMetadataLookup, carrierSource⟩
    exact
      retainedFinalDirectSourceRouteChoice_eq_none_of_fallbackMetadata
        formula taggedClause.2 taggedLiteral.2 metadata
        finalMetadataLookup (Or.inl carrierSource)
  calc
    retainedFinalCopiedClauseDescriptors
          (retainedFinalIndexedClauseQueriesFrom formula
            crossoverClauses.length carrierClauses) =
        carrierClauses.map (representativeClauseDescriptor formula) :=
      retainedFinalCopiedClauseDescriptors_indexedFrom_eq_representative
        formula crossoverClauses.length carrierClauses
        clauseLookups choicesNone
    _ = carrierMetadataClauseDescriptors formula := by
      simpa only [carrierClauses,
        PeriodicThreeSATThree.formulaCarrierMetadataNormalizedClauses,
        formula] using
        carrierMetadataNormalizedClauses_map_representative_eq_descriptors
          formula formulaWellFormed formulaDegree formulaLocal

end PeriodicEightOccurrenceSplit
end LeanTrominoes
