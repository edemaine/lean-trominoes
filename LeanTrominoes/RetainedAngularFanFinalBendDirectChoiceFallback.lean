/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalBendMetadataSemantics
import LeanTrominoes.RetainedAngularFanFinalBendTaggedBendInputLookup
import LeanTrominoes.RetainedAngularFanFinalDirectSourceChoiceFallback

/-! # Final direct-choice rejection for retained bends -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing
open PeriodicThreeSATThree

local instance finalBendDirectChoiceThreeOccurrenceDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq (ThreeOccurrenceVariable Variable) :=
  fiveFamilyNormalizedThreeOccurrenceDecidableEq

/-- Every literal of an indexed final retained-bend clause rejects the
direct Figure 7 atlas and therefore takes the fallback router. -/
theorem FinalBendTaggedBendInput.routeChoice_eq_none
    {Variable : Type} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    {taggedBend : RouteBend × Bool}
    {clauseIndex : Nat}
    (input : FinalBendTaggedBendInput
      source taggedBend clauseIndex)
    (literalIndex : Nat) :
    retainedFinalDirectSourceRouteChoice?
        (PeriodicThreeSATThree.formula source)
        clauseIndex literalIndex = none := by
  let retained := PeriodicThreeSATThree.formula source
  let clause := normalizedBendClauseAt retained taggedBend
  have indexed := input.taggedBendIndexed
  unfold finalBendTaggedBendIndexed at indexed
  have taggedBendMember : taggedBend ∈
      ((baseRouteBends retained).product [true, false]) :=
    List.fst_mem_of_mem_zipIdx indexed
  have bendMember : clause ∈ baseBendNormalizedClauses retained := by
    rw [baseBendNormalizedClauses_eq_map_baseTaggedBends]
    exact List.mem_map.mpr
      ⟨taggedBend, taggedBendMember, rfl⟩
  have retainedWellFormed : retained.incidenceGraph.IsWellFormed :=
    formula_incidenceGraph_isWellFormed source
  have retainedDegree : retained.incidenceGraph.DegreeAtMost 3 :=
    formula_incidenceGraph_degreeAtMostThree
      input.sourceInput.sourceFacts.nonemptyFacts.widthFacts.sourceWidth
  have retainedLocal : retained.incidenceGraph.IsLocal :=
    formula_incidenceGraph_isLocal
      input.sourceInput.sourceFacts.nonemptyFacts.widthFacts.localFacts.sourceLocal
  rcases exists_finalBendMetadata_of_clause_lookup
      retained retainedWellFormed retainedDegree retainedLocal
      clauseIndex clause input.clauseLookup bendMember with
    ⟨metadata, metadataLookup, bendSource⟩
  exact retainedFinalDirectSourceRouteChoice_eq_none_of_fallbackMetadata
    retained clauseIndex literalIndex metadata metadataLookup
      (Or.inr bendSource)

end PeriodicEightOccurrenceSplit
end LeanTrominoes
