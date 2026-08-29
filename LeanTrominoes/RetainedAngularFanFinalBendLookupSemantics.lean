/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataNormalizedBendRepresentativeDescriptors
import LeanTrominoes.PeriodicThreeSATThreeBendClauseLookup

/-! # Exact final clause lookup for retained bends -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing
open PeriodicThreeSATThree

local instance finalBendLookupThreeOccurrenceDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq (ThreeOccurrenceVariable Variable) :=
  fiveFamilyNormalizedThreeOccurrenceDecidableEq

/-- The global final-bend index relation between one untranslated routed bend
and implication and its position after the crossover and carrier prefixes. -/
def finalBendTaggedBendIndexed
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (taggedBend : RouteBend × Bool)
    (clauseIndex : Nat) : Prop :=
  let retained := PeriodicThreeSATThree.formula source
  (taggedBend, clauseIndex) ∈
    ((baseRouteBends retained).product [true, false]).zipIdx
      ((crossoverMetadataNormalizedClausesDedup retained).length +
        (formulaCarrierMetadataNormalizedClauses source).length)

/-- Every tagged untranslated bend implication occupies its declared global
index in the final duplicate-free retained clause presentation. -/
theorem finalBendClause_lookup
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceClausesNonempty : ∀ clause ∈ source.clauses, clause ≠ [])
    (positiveOffsets : ∀ incidence ∈ occurrenceIncidences source,
      incidence.edge.offset = (0, 0) ∨
        incidence.edge.offset = (1, 0))
    (taggedBend : RouteBend × Bool)
    (clauseIndex : Nat)
    (taggedBendIndexed :
      finalBendTaggedBendIndexed source taggedBend clauseIndex) :
    let retained := PeriodicThreeSATThree.formula source
    (deduplicatedClauses retained)[clauseIndex]? =
      some (normalizedBendClauseAt retained taggedBend) := by
  let retained := PeriodicThreeSATThree.formula source
  let taggedBends := (baseRouteBends retained).product [true, false]
  let clause := normalizedBendClauseAt retained taggedBend
  unfold finalBendTaggedBendIndexed at taggedBendIndexed
  have mappedIndexed : (clause, clauseIndex) ∈
      (taggedBends.map (normalizedBendClauseAt retained)).zipIdx
        ((crossoverMetadataNormalizedClausesDedup retained).length +
          (formulaCarrierMetadataNormalizedClauses source).length) := by
    rw [List.zipIdx_map]
    exact List.mem_map.mpr
      ⟨(taggedBend, clauseIndex), taggedBendIndexed, rfl⟩
  have taggedClauseIndexed : (clause, clauseIndex) ∈
      (formulaBaseBendNormalizedClauses source).zipIdx
        ((crossoverMetadataNormalizedClausesDedup retained).length +
          (formulaCarrierMetadataNormalizedClauses source).length) := by
    simpa only [retained, taggedBends, clause,
      formulaBaseBendNormalizedClauses,
      baseBendNormalizedClauses_eq_map_baseTaggedBends] using
        mappedIndexed
  simpa only [retained, clause] using
    formulaBaseBendNormalizedClauses_getElem?_of_mem_zipIdx
      source sourceLocal sourceWidth sourceClausesNonempty
        positiveOffsets (clause, clauseIndex) taggedClauseIndexed

end PeriodicEightOccurrenceSplit
end LeanTrominoes
