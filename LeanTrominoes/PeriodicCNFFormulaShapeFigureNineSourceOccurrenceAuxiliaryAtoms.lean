/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PlanarOneInThreeNoUnitsFigureNineAuxiliaryIdentity
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineSourceOccurrenceLiteralAtoms

/-! # Genuine Figure 9 occurrences preserve auxiliary atom identity -/

namespace LeanTrominoes.PeriodicCNF.FormulaShapeRetainedFigureNineSourceTail

open FormulaShapeFigureNinePolarityRouteTail
open FormulaShapeFigureNineRoutePrefix
open PlanarOneInThreeNoUnitsFigureNine
open PeriodicOrthocrossing

private theorem localQuery_unitAux_bound : ∀ query : LocalDirectionQuery,
    match ((templateDrawingOfClauseProfile query.1).incidenceAt query.2).literal.1 with
    | .unitAux index _ => index < 6 - query.1.literals.length
    | .inherited _ => True := by
  have checked : ∀ query : LocalDirectionQuery,
      (match ((templateDrawingOfClauseProfile query.1).incidenceAt query.2).literal.1 with
      | .unitAux index _ => decide (index < 6 - query.1.literals.length)
      | .inherited _ => true) = true := by
    native_decide
  intro query
  have bound := checked query
  cases selected : ((templateDrawingOfClauseProfile query.1).incidenceAt query.2).literal.1 with
  | unitAux index kind => simpa only [selected, decide_eq_true_eq] using bound
  | inherited role => trivial

private theorem figureNineClauseGadget_length
    {Variable : Type} (parent : Nat) (source : PositionedPeriodicClause Variable)
    (nonempty : source.literals ≠ []) (width : source.literals.length ≤ 3) :
    (PeriodicOneInThreePositioned.clauseGadget parent source).length =
      6 - source.literals.length := by
  rcases source with ⟨position, literals⟩
  rcases literals with _ | ⟨first, rest⟩
  · exact (nonempty rfl).elim
  · rcases rest with _ | ⟨second, rest⟩
    · rfl
    · rcases rest with _ | ⟨third, rest⟩
      · rfl
      · have restEmpty : rest = [] := by
          apply List.length_eq_zero_iff.mp
          simp only [List.length_cons] at width
          omega
        subst rest
        rfl

/-- A selected unit-elimination auxiliary belongs to an actual first-stage
Figure 9 clause of this occurrence's own parent. -/
theorem OccurrenceWitness.unitAux_index_lt
    {Variable : Type} [DecidableEq Variable]
    {source : PeriodicCNF Variable} {occurrence : SourceOccurrence}
    (witness : OccurrenceWitness source occurrence) (index : Nat) (kind : OneInThreeNoUnitAux)
    (selected :
      ((templateDrawingOfClauseProfile occurrence.header.figurePrefix.localQuery.1).incidenceAt
        occurrence.header.figurePrefix.localQuery.2).literal.1 = .unitAux index kind) :
    index < (PeriodicOneInThreePositioned.clauseGadget
      witness.metadata.sourceClauseIndex witness.metadata.sourceClause).length := by
  have sourceLength : witness.metadata.sourceClause.literals.length =
      witness.refinedClause.literals.length := by
    simp only [witness.metadataSource, PositionedPeriodicClause.scale_literals,
      PositionedPeriodicCNF.orderClauseByRouteDirection_length]
  have sourceWidth : witness.metadata.sourceClause.literals.length ≤ 3 := by
    rw [sourceLength]
    exact witness.refinedWidth
  have sourceNonempty : witness.metadata.sourceClause.literals ≠ [] := by
    intro empty
    have lengthZero : witness.refinedClause.literals.length = 0 := by
      rw [← sourceLength, empty]
      rfl
    exact witness.refinedNonempty (List.length_eq_zero_iff.mp lengthZero)
  have profilesEq := FormulaShapeOfFormula.clauseProfile_literals
    (ClauseProfileOccurrenceSplit.literalProfiles witness.metadata.sourceClause.literals)
    (by simpa [ClauseProfileOccurrenceSplit.literalProfiles] using sourceNonempty)
    (by simpa [ClauseProfileOccurrenceSplit.literalProfiles] using sourceWidth)
  have profileEq := witness.metadataCoordinates.1
  change occurrence.header.figurePrefix.localQuery.1 =
    witness.metadata.parentProfileCoordinate.profile at profileEq
  have profileLength : occurrence.header.figurePrefix.localQuery.1.literals.length =
      witness.metadata.sourceClause.literals.length := by
    rw [profileEq]
    simpa only [ClauseMetadata.parentProfileCoordinate,
      ClauseProfileOccurrenceSplit.literalProfiles, List.length_map] using congrArg List.length profilesEq
  have bound := localQuery_unitAux_bound occurrence.header.figurePrefix.localQuery
  rw [selected] at bound
  change index < 6 - occurrence.header.figurePrefix.localQuery.1.literals.length at bound
  rw [profileLength] at bound
  rwa [figureNineClauseGadget_length _ _ sourceNonempty sourceWidth]

/-- Auxiliary atoms instantiated from genuine occurrences are equal exactly
when the parent index and finite template role agree. -/
theorem OccurrenceWitness.auxiliaryAtom_eq_iff
    {Variable : Type} [DecidableEq Variable]
    {source : PeriodicCNF Variable} {first second : SourceOccurrence}
    (firstWitness : OccurrenceWitness source first)
    (secondWitness : OccurrenceWitness source second)
    (firstAuxiliary : sourceSlot?
      ((templateDrawingOfClauseProfile first.header.figurePrefix.localQuery.1).incidenceAt
        first.header.figurePrefix.localQuery.2).literal.1 = none)
    (secondAuxiliary : sourceSlot?
      ((templateDrawingOfClauseProfile second.header.figurePrefix.localQuery.1).incidenceAt
        second.header.figurePrefix.localQuery.2).literal.1 = none) :
    let firstRole := ((templateDrawingOfClauseProfile first.header.figurePrefix.localQuery.1).incidenceAt
      first.header.figurePrefix.localQuery.2).literal.1
    let secondRole := ((templateDrawingOfClauseProfile second.header.figurePrefix.localQuery.1).incidenceAt
      second.header.figurePrefix.localQuery.2).literal.1
    instantiatedVariableMap firstWitness.metadata.sourceClauseIndex
        firstWitness.metadata.figureNineClauseStart firstWitness.metadata.sourceClause firstRole =
      instantiatedVariableMap secondWitness.metadata.sourceClauseIndex
        secondWitness.metadata.figureNineClauseStart secondWitness.metadata.sourceClause secondRole ↔
      (first.parentClauseIndex, firstRole) = (second.parentClauseIndex, secondRole) := by
  dsimp only
  have identity := instantiatedVariableMap_auxiliary_eq_iff
    (retainedFigureNineClearancePositionedFormula source)
    (List.mem_iff_getElem?.mpr ⟨first.generatedClauseIndex, firstWitness.metadataLookup⟩)
    (List.mem_iff_getElem?.mpr ⟨second.generatedClauseIndex, secondWitness.metadataLookup⟩)
    _ _ firstAuxiliary secondAuxiliary firstWitness.unitAux_index_lt secondWitness.unitAux_index_lt
  have firstParent : firstWitness.metadata.sourceClauseIndex = first.parentClauseIndex :=
    congrArg Prod.fst firstWitness.metadataKey
  have secondParent : secondWitness.metadata.sourceClauseIndex = second.parentClauseIndex :=
    congrArg Prod.fst secondWitness.metadataKey
  exact identity.trans (by rw [firstParent, secondParent])

end LeanTrominoes.PeriodicCNF.FormulaShapeRetainedFigureNineSourceTail
