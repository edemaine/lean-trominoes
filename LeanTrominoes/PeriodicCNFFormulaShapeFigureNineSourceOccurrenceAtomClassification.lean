/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineSourceOccurrenceLiteralAtoms
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineRoutePrefixInstantiationSemantics

/-! # Inherited and auxiliary classes of actual Figure 9 atoms -/

namespace LeanTrominoes.PlanarOneInThreeNoUnitsFigureNine

open PeriodicCNF.FormulaShapeFigureNineRoutePrefix

/-- In a nonempty parent, precisely the source-port roles instantiate to
inherited variables. This includes the selector's inactive-port defaults. -/
theorem instantiatedVariableMap_inherited_iff
    {Variable : Type} (parent start : Nat) (source : PositionedPeriodicClause Variable)
    (nonempty : source.literals ≠ []) (role : FigureNineNoUnitsVariable) :
    (∃ atom, instantiatedVariableMap parent start source role = .inl (.inl atom)) ↔
      ∃ slot, sourceSlot? role = some slot := by
  constructor
  · rintro ⟨atom, equal⟩
    cases selected : sourceSlot? role with
    | none => exact (instantiatedVariableMap_not_inherited_of_sourceSlot_none
        parent start source role selected atom equal).elim
    | some slot => exact ⟨slot, rfl⟩
  · rintro ⟨slot, selected⟩
    cases role with
    | unitAux index kind => simp [sourceSlot?] at selected
    | inherited role =>
        rcases source with ⟨position, literals⟩
        rcases literals with _ | ⟨first, rest⟩
        · exact (nonempty rfl).elim
        · rcases rest with _ | ⟨second, rest⟩
          · cases role <;> simp_all [sourceSlot?, instantiatedVariableMap, oneVariableMap,
              variableMap, oneInheritedMap]
          · rcases rest with _ | ⟨third, rest⟩ <;>
              cases role <;> simp_all [sourceSlot?, instantiatedVariableMap,
                twoVariableMap, threeVariableMap, variableMap, twoInheritedMap, threeInheritedMap]

end LeanTrominoes.PlanarOneInThreeNoUnitsFigureNine

namespace LeanTrominoes.PeriodicCNF.FormulaShapeRetainedFigureNineSourceTail

open FormulaShapeFigureNinePolarityRouteTail
open FormulaShapeFigureNineRoutePrefix
open PlanarOneInThreeNoUnitsFigureNine

/-- The actual parent of an occurrence is nonempty, as certified before
clockwise ordering and clearance scaling. -/
theorem OccurrenceWitness.sourceClause_nonempty
    {Variable : Type} [DecidableEq Variable]
    {source : PeriodicCNF Variable} {occurrence : SourceOccurrence}
    (witness : OccurrenceWitness source occurrence) :
    witness.metadata.sourceClause.literals ≠ [] := by
  have lengthEq : witness.metadata.sourceClause.literals.length =
      witness.refinedClause.literals.length := by
    simp only [witness.metadataSource, PositionedPeriodicClause.scale_literals,
      PositionedPeriodicCNF.orderClauseByRouteDirection_length]
  intro empty
  apply witness.refinedNonempty
  apply List.length_eq_zero_iff.mp
  rw [← lengthEq, empty]
  rfl

/-- The finite source-slot classification is the inherited/auxiliary
constructor classification of the actual instantiated atom. -/
theorem OccurrenceWitness.instantiatedAtom_inherited_iff
    {Variable : Type} [DecidableEq Variable]
    {source : PeriodicCNF Variable} {occurrence : SourceOccurrence}
    (witness : OccurrenceWitness source occurrence) :
    let role := ((templateDrawingOfClauseProfile occurrence.header.figurePrefix.localQuery.1).incidenceAt
      occurrence.header.figurePrefix.localQuery.2).literal.1
    (∃ atom, instantiatedVariableMap witness.metadata.sourceClauseIndex
      witness.metadata.figureNineClauseStart witness.metadata.sourceClause role = .inl (.inl atom)) ↔
      ∃ slot, sourceSlot? role = some slot := by
  exact instantiatedVariableMap_inherited_iff _ _ _ witness.sourceClause_nonempty _

end LeanTrominoes.PeriodicCNF.FormulaShapeRetainedFigureNineSourceTail
