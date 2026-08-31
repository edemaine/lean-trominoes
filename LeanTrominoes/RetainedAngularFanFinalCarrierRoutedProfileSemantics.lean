/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCarrierCopiedProfileSemantics
import LeanTrominoes.RetainedAngularFanFinalCoordinatedIndexedClauseLookup
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseProfileExtensionality
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFigureNineCopiedDirectionSemantics
import LeanTrominoes.BinaryRouteTailRecordFormatterData
import LeanTrominoes.PeriodicThreeSATThreeRoutedVariableRotatedEdgeIndexDedup

/-! # Routed copied-clause profiles of final retained carriers -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing
open PlanarThreeSAT
open PeriodicThreeSATThree

local instance finalCarrierRoutedProfileThreeOccurrenceDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq (ThreeOccurrenceVariable Variable) :=
  fiveFamilyNormalizedThreeOccurrenceDecidableEq

/-- The semantic route-based profile at an indexed final carrier is the
profile stored by its canonical equality-lens compiler block. -/
theorem FinalCarrierTaggedLinkInput.routedProfile_eq_carrier
    {Variable : Type} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    {taggedLink : EqualityLink CarrierNode × Bool}
    {clauseIndex : Nat}
    (input : FinalCarrierTaggedLinkInput
      source taggedLink clauseIndex) :
    PeriodicCNF.FormulaShapeRetainedFigureNineDirection.routedCopiedClauseProfile
        (PeriodicThreeSATThree.formula source)
        clauseIndex
        ⟨(0, 0), normalizedCarrierClauseAt
          (PeriodicThreeSATThree.formula source) taggedLink⟩ =
      BinaryRouteTailRecordFormatter.descriptorProfile
        (carrierClauseDescriptor taggedLink.1.first.isHorizontal
          (carrierLinkNextSlice
            (PeriodicThreeSATThree.formula source) taggedLink.1)
          taggedLink.2) := by
  let retained := PeriodicThreeSATThree.formula source
  let clause := normalizedCarrierClauseAt retained taggedLink
  let normalizedPositioned : PositionedPeriodicClause
      (WrappedPeriodicPlanarSATVariable
        (ThreeOccurrenceVariable Variable)) := ⟨(0, 0), clause⟩
  rcases exists_finalCoordinatedPositionedClause_of_lookup
      retained clauseIndex clause input.clauseLookup with
    ⟨positionedClause, positionedLookup, literalsEq⟩
  have positionedMember : (positionedClause, clauseIndex) ∈
      (finalCoordinatedSource retained).clauses.zipIdx :=
    (List.mem_zipIdx_iff_getElem?).mpr positionedLookup
  have routedEqCopied :=
    PeriodicCNF.FormulaShapeRetainedFigureNineDirection.routedCopiedClauseProfile_eq_copiedClauseProfile
      retained
      (PeriodicThreeSATThree.formula_isLocal
        input.sourceInput.sourceFacts.nonemptyFacts.widthFacts.localFacts.sourceLocal)
      (PeriodicThreeSATThree.formula_widthAtMostThree
        input.sourceInput.sourceFacts.nonemptyFacts.widthFacts.sourceWidth)
      (PeriodicThreeSATThree.formula_occurrencesAtMostThree_decidableEq source)
      (PeriodicThreeSATThree.formula_clausesNonempty source
        input.sourceInput.sourceFacts.nonemptyFacts.sourceClausesNonempty)
      positionedMember
  have copiedProfileEq :
      PeriodicCNF.FormulaShapeRetainedFigureNineDirection.copiedClauseProfile
          retained clauseIndex normalizedPositioned =
        BinaryRouteTailRecordFormatter.descriptorProfile
          (carrierClauseDescriptor taggedLink.1.first.isHorizontal
            (carrierLinkNextSlice retained taggedLink.1)
            taggedLink.2) := by
    have tokenEq := congrArg BinaryRouteTailRecordFormatter.descriptorProfile
      input.copiedDescriptor_eq_carrier
    simpa only [BinaryRouteTailRecordFormatter.descriptorProfile,
      carrierClauseDescriptor] using tokenEq
  calc
    PeriodicCNF.FormulaShapeRetainedFigureNineDirection.routedCopiedClauseProfile
          retained clauseIndex normalizedPositioned =
        PeriodicCNF.FormulaShapeRetainedFigureNineDirection.routedCopiedClauseProfile
          retained clauseIndex positionedClause :=
      PeriodicCNF.FormulaShapeRetainedFigureNineDirection.routedCopiedClauseProfile_eq_of_literals_eq
        retained clauseIndex normalizedPositioned positionedClause
        literalsEq.symm
    _ = PeriodicCNF.FormulaShapeRetainedFigureNineDirection.copiedClauseProfile
          retained clauseIndex positionedClause := routedEqCopied
    _ = PeriodicCNF.FormulaShapeRetainedFigureNineDirection.copiedClauseProfile
          retained clauseIndex normalizedPositioned :=
      PeriodicCNF.FormulaShapeRetainedFigureNineDirection.copiedClauseProfile_eq_of_literals_eq
        retained clauseIndex positionedClause normalizedPositioned literalsEq
    _ = _ := copiedProfileEq

end PeriodicEightOccurrenceSplit
end LeanTrominoes
