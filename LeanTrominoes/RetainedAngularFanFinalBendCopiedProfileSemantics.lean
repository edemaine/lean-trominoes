/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataBendNextSliceSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataNormalizedBendRepresentativeDescriptors
import LeanTrominoes.RetainedAngularFanFinalBendDirectChoiceFallback
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseQueryFallbackSemantics

/-! # Copied-clause profiles of final retained bends -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing
open PlanarThreeSAT
open PeriodicThreeSATThree

local instance finalBendCopiedProfileThreeOccurrenceDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq (ThreeOccurrenceVariable Variable) :=
  fiveFamilyNormalizedThreeOccurrenceDecidableEq

/-- The finite copied-clause descriptor at an indexed final bend is its
canonical untranslated corner descriptor. -/
theorem FinalBendTaggedBendInput.copiedDescriptor_eq_bend
    {Variable : Type} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    {taggedBend : RouteBend × Bool}
    {clauseIndex : Nat}
    (input : FinalBendTaggedBendInput
      source taggedBend clauseIndex) :
    .clause
        (PeriodicCNF.FormulaShapeRetainedFigureNineDirection.copiedClauseProfile
          (PeriodicThreeSATThree.formula source)
          clauseIndex
          ⟨(0, 0), normalizedBendClauseAt
            (PeriodicThreeSATThree.formula source) taggedBend⟩) =
      bendClauseDescriptor
        taggedBend.1.incomingPort taggedBend.1.outgoingPort
        false taggedBend.2 := by
  let retained := PeriodicThreeSATThree.formula source
  let clause := normalizedBendClauseAt retained taggedBend
  let positionedClause : PositionedPeriodicClause
      (WrappedPeriodicPlanarSATVariable
        (ThreeOccurrenceVariable Variable)) := ⟨(0, 0), clause⟩
  have indexed := input.taggedBendIndexed
  unfold finalBendTaggedBendIndexed at indexed
  have baseTaggedMember : taggedBend ∈
      (baseRouteBends retained).product [true, false] :=
    List.fst_mem_of_mem_zipIdx indexed
  have routeBendMember : taggedBend.1 ∈ baseRouteBends retained :=
    (List.mem_product.mp baseTaggedMember).1
  have taggedBendMember : taggedBend ∈
      ((drawingRouteBends retained.incidenceGraph).dedup).product
        [true, false] :=
    List.mem_product.mpr
      ⟨baseRouteBends_subset_drawing retained routeBendMember,
        (List.mem_product.mp baseTaggedMember).2⟩
  have choicesNone : ∀ taggedLiteral ∈ clause.zipIdx,
      retainedFinalDirectSourceRouteChoice?
          retained clauseIndex taggedLiteral.2 = none := by
    intro taggedLiteral _taggedLiteralMember
    exact input.routeChoice_eq_none taggedLiteral.2
  have retainedWellFormed : retained.incidenceGraph.IsWellFormed :=
    formula_incidenceGraph_isWellFormed source
  have retainedDegree : retained.incidenceGraph.DegreeAtMost 3 :=
    formula_incidenceGraph_degreeAtMostThree
      input.sourceInput.sourceFacts.nonemptyFacts.widthFacts.sourceWidth
  have retainedLocal : retained.incidenceGraph.IsLocal :=
    formula_incidenceGraph_isLocal
      input.sourceInput.sourceFacts.nonemptyFacts.widthFacts.localFacts.sourceLocal
  calc
    .clause
          (PeriodicCNF.FormulaShapeRetainedFigureNineDirection.copiedClauseProfile
            retained clauseIndex positionedClause) =
        retainedFinalCopiedClauseDescriptorOfQuery
          (retainedFinalCopiedClauseQueryOfLiterals
            retained clauseIndex clause) := by
      exact (retainedFinalCopiedClauseDescriptorOfQuery_eq
        retained clauseIndex positionedClause).symm
    _ = representativeClauseDescriptor retained clause :=
      retainedFinalCopiedClauseDescriptorOfQuery_eq_representative_of_choices_none
        retained clauseIndex clause input.clauseLookup choicesNone
    _ = normalizedBendClauseDescriptorAt retained taggedBend :=
      representativeClauseDescriptor_eq_normalizedBend
        retained retainedWellFormed retainedDegree retainedLocal
        taggedBend taggedBendMember
    _ = bendClauseDescriptor
          taggedBend.1.incomingPort taggedBend.1.outgoingPort
          false taggedBend.2 := by
      unfold normalizedBendClauseDescriptorAt
      rw [metadataClauseDescriptor_bendClauseMetadataAt_eq,
        bendLinkNextSlice_eq_false]

end PeriodicEightOccurrenceSplit
end LeanTrominoes
