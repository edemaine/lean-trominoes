/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeBendClauseLookup
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataNormalizedBendRepresentativeDescriptors
import LeanTrominoes.RetainedAngularFanFinalBendMetadataSemantics
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseQueryFallbackListSemantics
import LeanTrominoes.RetainedAngularFanFinalDirectSourceChoiceFallback

/-! # Exact final copied-query semantics for retained bends -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

local instance finalBendQueryThreeOccurrenceDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq (ThreeOccurrenceVariable Variable) :=
  PeriodicThreeSATThree.fiveFamilyNormalizedThreeOccurrenceDecidableEq

/-- The exact final queries occupying the canonical base-bend subfamily
evaluate to the established base-bend metadata descriptor stream. -/
theorem retainedFinalBendClauseQueryDescriptors_formula_eq
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
    let bendClauses :=
      PeriodicThreeSATThree.formulaBaseBendNormalizedClauses source
    retainedFinalCopiedClauseDescriptors
        (retainedFinalIndexedClauseQueriesFrom formula
          (crossoverClauses.length + carrierClauses.length)
          bendClauses) =
      baseBendClauseDescriptors formula := by
  dsimp only
  let formula := PeriodicThreeSATThree.formula source
  let crossoverClauses :=
    crossoverMetadataNormalizedClausesDedup formula
  let carrierClauses :=
    PeriodicThreeSATThree.formulaCarrierMetadataNormalizedClauses source
  let bendClauses :=
    PeriodicThreeSATThree.formulaBaseBendNormalizedClauses source
  have formulaWellFormed : formula.incidenceGraph.IsWellFormed :=
    PeriodicThreeSATThree.formula_incidenceGraph_isWellFormed source
  have formulaDegree : formula.incidenceGraph.DegreeAtMost 3 :=
    PeriodicThreeSATThree.formula_incidenceGraph_degreeAtMostThree
      sourceWidth
  have formulaLocal : formula.incidenceGraph.IsLocal :=
    PeriodicThreeSATThree.formula_incidenceGraph_isLocal sourceLocal
  have clauseLookups :
      ∀ taggedClause ∈ bendClauses.zipIdx
          (crossoverClauses.length + carrierClauses.length),
        (deduplicatedClauses formula)[taggedClause.2]? =
          some taggedClause.1 := by
    intro taggedClause taggedClauseMember
    simpa only [formula, crossoverClauses, carrierClauses,
      bendClauses] using
      PeriodicThreeSATThree.formulaBaseBendNormalizedClauses_getElem?_of_mem_zipIdx
        source sourceLocal sourceWidth sourceClausesNonempty
          positiveOffsets taggedClause taggedClauseMember
  have choicesNone :
      ∀ taggedClause ∈ bendClauses.zipIdx
          (crossoverClauses.length + carrierClauses.length),
        ∀ taggedLiteral ∈ taggedClause.1.zipIdx,
          retainedFinalDirectSourceRouteChoice?
              formula taggedClause.2 taggedLiteral.2 = none := by
    intro taggedClause taggedClauseMember taggedLiteral _taggedLiteralMember
    have clauseLookup := clauseLookups taggedClause taggedClauseMember
    have bendMember :
        taggedClause.1 ∈ baseBendNormalizedClauses formula := by
      exact List.fst_mem_of_mem_zipIdx taggedClauseMember
    rcases
        exists_finalBendMetadata_of_clause_lookup
          formula formulaWellFormed formulaDegree formulaLocal
          taggedClause.2 taggedClause.1 clauseLookup bendMember with
      ⟨metadata, finalMetadataLookup, bendSource⟩
    exact
      retainedFinalDirectSourceRouteChoice_eq_none_of_fallbackMetadata
        formula taggedClause.2 taggedLiteral.2 metadata
        finalMetadataLookup (Or.inr bendSource)
  calc
    retainedFinalCopiedClauseDescriptors
          (retainedFinalIndexedClauseQueriesFrom formula
            (crossoverClauses.length + carrierClauses.length)
            bendClauses) =
        bendClauses.map (representativeClauseDescriptor formula) :=
      retainedFinalCopiedClauseDescriptors_indexedFrom_eq_representative
        formula (crossoverClauses.length + carrierClauses.length)
        bendClauses clauseLookups choicesNone
    _ = baseBendClauseDescriptors formula := by
      simpa only [bendClauses,
        PeriodicThreeSATThree.formulaBaseBendNormalizedClauses,
        formula] using
        baseBendNormalizedClauses_map_representative_eq_descriptors
          formula formulaWellFormed formulaDegree formulaLocal

end PeriodicEightOccurrenceSplit
end LeanTrominoes
