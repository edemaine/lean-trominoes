/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCycleCoordinateCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalAtomValueRows

/-! # Cycle coordinate rows select the actual inherited parent literals -/

noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open PeriodicCNF PeriodicOrthocrossing PeriodicEightOccurrenceSplit OccurrenceSplitRing
open PeriodicCNF.FormulaShapeDirectionOrdering
open HorizontalRoutedRouteHeaderPresentationAtomScope
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteHeader
open PeriodicCNF.ClauseProfilePolarityRouteOperation

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance cycleCoordinateSemanticStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack
attribute [local instance] directSourceVariableDecidableEqInstance

/-- Each owner block uses the actual local cycle clauses in presentation order.
Parent-local scopes retain the inherited column's default vertex. -/
theorem directSourceFinalCycleCoordinateCopies_eq_literal_blocks (symbols : List encoding.Γ) :
    directSourceFinalCycleCoordinateCopies decider symbols =
      (directSourceFinalCycleCoordinateOwners decider symbols).flatMap fun atom =>
        FormulaShapeFixedEightDirection.localCycleFormula.clauses.zipIdx.flatMap fun tagged =>
          (clauseBlock (DirectedClauseProfile.ofClause cycleRoutes tagged.2 tagged.1)).map fun control =>
            ringCopy atom (directFinalCycleRingVertexOfSlot (directFinalCycleLiteralSlot tagged.1 control)) := by
  unfold directSourceFinalCycleCoordinateCopies directSourceFinalCycleCoordinateEntries
  rw [directSourceFinalLocalCycleRingVertexSlots_eq_literal_blocks]
  simp only [List.map_flatMap, List.map_map, Function.comp_def]

/-- The coordinate and identity streams refer to precisely the same ring copies,
including the separator and the unused parent-local default entries. -/
theorem directSourceFinalCycleCoordinateCopies_eq_codes (symbols : List encoding.Γ) :
    (directSourceFinalCycleCoordinateCopies decider symbols).map
        (directSourceFinalRingVariableCode decider symbols) =
      directSourceFinalCycleInheritedRingAtomCodes decider symbols := by
  rw [directSourceFinalCycleInheritedRingAtomCodes_eq_actual_atoms]
  unfold directSourceFinalCycleCoordinateCopies directSourceFinalCycleCoordinateEntries
    directSourceFinalCycleCoordinateOwners
  simp only [List.map_flatMap, List.map_map, Function.comp_def]
  apply List.flatMap_congr
  intro atom _member
  apply List.map_congr_left
  intro slot _slotMember
  rw [directSourceFinalRingVariableCode_ringCopy, directFinalCycleRingVertexSlot_ofSlot]

/-- Coordinate output in actual local-clause and final scope order. The
inherited cases are identified with active literal rows below. -/
theorem directSourceFinalCycleCoordinates_eq_literal_blocks
    (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    directSourceFinalCycleCoordinates decider horizontal keepPositive symbols =
      (directSourceFinalCycleCoordinateOwners decider symbols).flatMap fun atom =>
        FormulaShapeFixedEightDirection.localCycleFormula.clauses.zipIdx.flatMap fun tagged =>
          (clauseBlock (DirectedClauseProfile.ofClause cycleRoutes tagged.2 tagged.1)).map fun control =>
            CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal keepPositive)
              ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
                (directSourceFormula decider symbols)).position
                (ringCopy atom (directFinalCycleRingVertexOfSlot (directFinalCycleLiteralSlot tagged.1 control)))) := by
  rw [directSourceFinalCycleCoordinates_eq_positions,
    directSourceFinalCycleCoordinateCopies_eq_literal_blocks]
  simp only [List.map_flatMap, List.map_map, Function.comp_def]

/-- Actual split-placement coordinates grouped by cycle parent clause. -/
def directSourceFinalCycleCoordinateValueBlocks
    (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    List (DirectedClauseProfile × SourceOccurrenceAtomValueRow) :=
  (directSourceFinalCycleCoordinateOwners decider symbols).flatMap fun atom =>
    FormulaShapeFixedEightDirection.localCycleFormula.clauses.zipIdx.map fun tagged =>
      let value := fun vertex => CarrierCrossingPointField.pointValue
        (coordinateFieldOfBools horizontal keepPositive)
        ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
          (directSourceFormula decider symbols)).position (ringCopy atom vertex))
      (DirectedClauseProfile.ofClause cycleRoutes tagged.2 tagged.1,
        { literals := tagged.1.literals.map (fun literal => value literal.atom),
          localFallback := value (directFinalCycleRingVertexOfSlot default) })

private theorem cycleLiteral_value (value : RingVertex → Nat)
    (tagged : PositionedPeriodicClause RingVertex × Nat)
    (member : tagged ∈ FormulaShapeFixedEightDirection.localCycleFormula.clauses.zipIdx)
    (control : HorizontalRoutedRouteHeader.AtomScopeControl)
    (scope : control ∈ clauseBlock (DirectedClauseProfile.ofClause cycleRoutes tagged.2 tagged.1)) :
    value (directFinalCycleRingVertexOfSlot (directFinalCycleLiteralSlot tagged.1 control)) =
      ({ literals := tagged.1.literals.map (fun literal => value literal.atom),
         localFallback := value (directFinalCycleRingVertexOfSlot default) } :
        SourceOccurrenceAtomValueRow).value control := by
  cases control with
  | parentLocal _ => rfl
  | inherited slot =>
    have active := directFinalCycleLiteralSlot_inherited_active tagged member slot scope
    rw [directFinalCycleRingVertexOfSlot_literal_inherited tagged.1 slot active]
    simp only [SourceOccurrenceAtomValueRow.value]
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using active), List.getElem_map]

/-- Compiled cycle coordinates are the selected values of actual parent rows. -/
theorem directSourceFinalCycleCoordinates_eq_value_blocks
    (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    directSourceFinalCycleCoordinates decider horizontal keepPositive symbols =
      (directSourceFinalCycleCoordinateValueBlocks decider horizontal keepPositive symbols).flatMap
        (fun block => (clauseBlock block.1).map block.2.value) := by
  rw [directSourceFinalCycleCoordinates_eq_literal_blocks]
  simp only [directSourceFinalCycleCoordinateValueBlocks, List.flatMap_assoc, List.flatMap_map]
  apply List.flatMap_congr
  intro atom _atomMember
  apply List.flatMap_congr
  intro tagged member
  apply List.map_congr_left
  intro control scope
  exact cycleLiteral_value (fun vertex => CarrierCrossingPointField.pointValue
    (coordinateFieldOfBools horizontal keepPositive)
    ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
      (directSourceFormula decider symbols)).position (ringCopy atom vertex))) tagged member control scope

/-- The parent coordinate rows are exactly the literal rows of the actual
positioned cycle suffix, in retained source-atom and parent-clause order. -/
theorem directSourceFinalCycleCoordinateValueBlocks_literals
    (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    (directSourceFinalCycleCoordinateValueBlocks decider horizontal keepPositive symbols).map
        (fun block => block.2.literals) =
      (FormulaShapeRetainedFigureNineDirection.finalCycleClauses
        (directSourceFormula decider symbols)).map fun clause => clause.literals.map fun literal =>
          CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal keepPositive)
            ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
              (directSourceFormula decider symbols)).position literal.atom) := by
  let value := fun copy => CarrierCrossingPointField.pointValue
    (coordinateFieldOfBools horizontal keepPositive)
    ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
      (directSourceFormula decider symbols)).position copy)
  have mapped := congrArg (List.map (List.map value))
    (FormulaShapeRetainedFigureNineDirection.finalCycleClauses_atom_rows
      (directSourceFormula decider symbols))
  calc
    _ = (directSourceFinalCycleCoordinateOwners decider symbols).flatMap fun atom =>
        FormulaShapeFixedEightDirection.localCycleFormula.clauses.map fun clause =>
          clause.literals.map (fun literal => value (ringCopy atom literal.atom)) := by
      simp only [directSourceFinalCycleCoordinateValueBlocks, List.map_flatMap, List.map_map, Function.comp_def]
      apply List.flatMap_congr
      intro atom _member
      simpa only [List.map_map, Function.comp_def] using
        congrArg (List.map (fun clause => clause.literals.map
          (fun literal => value (ringCopy atom literal.atom))))
          (List.zipIdx_map_fst 0 FormulaShapeFixedEightDirection.localCycleFormula.clauses)
    _ = _ := by
      simpa only [directSourceFinalCycleCoordinateOwners, List.map_map, List.map_flatMap,
        Function.comp_def] using mapped.symm

end LeanTrominoes.PeriodicCNFStripReduction
end
