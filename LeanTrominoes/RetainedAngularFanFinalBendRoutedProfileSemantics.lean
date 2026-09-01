/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalBendCopiedProfileSemantics
import LeanTrominoes.RetainedAngularFanFinalCoordinatedIndexedClauseLookup
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseProfileExtensionality
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFigureNineCopiedDirectionSemantics
import LeanTrominoes.BinaryRouteTailRecordFormatterData
import LeanTrominoes.PeriodicThreeSATThreeRoutedVariableRotatedEdgeIndexDedup

/-! # Routed copied-clause profiles of final retained bends -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing
open PlanarThreeSAT
open PeriodicThreeSATThree

local instance finalBendRoutedProfileThreeOccurrenceDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq (ThreeOccurrenceVariable Variable) :=
  fiveFamilyNormalizedThreeOccurrenceDecidableEq

/-- The semantic route-based profile at an indexed final bend is the
profile stored by its canonical finite corner block. -/
theorem FinalBendTaggedBendInput.routedProfile_eq_bend
    {Variable : Type} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    {taggedBend : RouteBend × Bool}
    {clauseIndex : Nat}
    (input : FinalBendTaggedBendInput
      source taggedBend clauseIndex) :
    PeriodicCNF.FormulaShapeRetainedFigureNineDirection.routedCopiedClauseProfile
        (PeriodicThreeSATThree.formula source)
        clauseIndex
        ⟨(0, 0), normalizedBendClauseAt
          (PeriodicThreeSATThree.formula source) taggedBend⟩ =
      BinaryRouteTailRecordFormatter.descriptorProfile
        (bendClauseDescriptor
          taggedBend.1.incomingPort taggedBend.1.outgoingPort
          false taggedBend.2) := by
  let retained := PeriodicThreeSATThree.formula source
  let clause := normalizedBendClauseAt retained taggedBend
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
          (bendClauseDescriptor
            taggedBend.1.incomingPort taggedBend.1.outgoingPort
            false taggedBend.2) := by
    have tokenEq := congrArg BinaryRouteTailRecordFormatter.descriptorProfile
      input.copiedDescriptor_eq_bend
    simpa only [BinaryRouteTailRecordFormatter.descriptorProfile] using tokenEq
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
