/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierDescriptorSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataNormalizedCarrierRepresentativeDescriptors
import LeanTrominoes.RetainedAngularFanFinalCarrierDirectChoiceFallback
import LeanTrominoes.RetainedAngularFanFinalCarrierTaggedLinkInputLookup
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseQueryFallbackSemantics

/-! # Copied-clause profiles of final retained carriers -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing
open PlanarThreeSAT
open PeriodicThreeSATThree

local instance finalCarrierCopiedProfileThreeOccurrenceDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq (ThreeOccurrenceVariable Variable) :=
  fiveFamilyNormalizedThreeOccurrenceDecidableEq

/-- The finite copied-clause descriptor at an indexed final carrier is its
canonical equality-lens descriptor. -/
theorem FinalCarrierTaggedLinkInput.copiedDescriptor_eq_carrier
    {Variable : Type} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    {taggedLink : EqualityLink CarrierNode × Bool}
    {clauseIndex : Nat}
    (input : FinalCarrierTaggedLinkInput
      source taggedLink clauseIndex) :
    .clause
        (PeriodicCNF.FormulaShapeRetainedFigureNineDirection.copiedClauseProfile
          (PeriodicThreeSATThree.formula source)
          clauseIndex
          ⟨(0, 0), normalizedCarrierClauseAt
            (PeriodicThreeSATThree.formula source) taggedLink⟩) =
      carrierClauseDescriptor taggedLink.1.first.isHorizontal
        (carrierLinkNextSlice
          (PeriodicThreeSATThree.formula source) taggedLink.1)
        taggedLink.2 := by
  let retained := PeriodicThreeSATThree.formula source
  let clause := normalizedCarrierClauseAt retained taggedLink
  let positionedClause : PositionedPeriodicClause
      (WrappedPeriodicPlanarSATVariable
        (ThreeOccurrenceVariable Variable)) := ⟨(0, 0), clause⟩
  have taggedMember : taggedLink ∈
      (retainedDrawingCompleteCarrierLinks
        retained.incidenceGraph).product [true, false] := by
    exact List.fst_mem_of_mem_zipIdx input.taggedLinkIndexed.member
  have linkMember : taggedLink.1 ∈
      retainedDrawingCompleteCarrierLinks retained.incidenceGraph :=
    (List.mem_product.mp taggedMember).1
  have choicesNone : ∀ taggedLiteral ∈ clause.zipIdx,
      retainedFinalDirectSourceRouteChoice?
          retained clauseIndex taggedLiteral.2 = none := by
    intro taggedLiteral _taggedLiteralMember
    exact finalCoordinatedSourceCarrierRouteChoice_eq_none
      source
      input.sourceInput.sourceFacts.nonemptyFacts.widthFacts.localFacts.sourceLocal
      input.sourceInput.sourceFacts.nonemptyFacts.widthFacts.sourceWidth
      input.sourceInput.sourceFacts.nonemptyFacts.sourceClausesNonempty
      input.sourceInput.sourceFacts.positiveOffsets
      taggedLink clauseIndex input.taggedLinkIndexed taggedLiteral.2
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
    _ = normalizedCarrierClauseDescriptorAt retained taggedLink :=
      representativeClauseDescriptor_eq_normalizedCarrier
        retained retainedWellFormed retainedDegree retainedLocal
        taggedLink taggedMember
    _ = carrierClauseDescriptor taggedLink.1.first.isHorizontal
          (carrierLinkNextSlice retained taggedLink.1) taggedLink.2 := by
      unfold normalizedCarrierClauseDescriptorAt
      exact metadataClauseDescriptor_carrierClauseMetadataAt_eq
        retained retainedWellFormed retainedDegree retainedLocal
        taggedLink.1 linkMember taggedLink.2

end PeriodicEightOccurrenceSplit
end LeanTrominoes
