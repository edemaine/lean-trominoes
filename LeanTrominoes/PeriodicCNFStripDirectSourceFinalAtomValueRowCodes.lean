/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalAtomValueRows
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCycleRingLiteralSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceBlocks

/-! # Complete inherited codes are coherent parent-row lookups -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF.FormulaShapeDirectionOrdering
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteTail
open PeriodicCNF.FormulaShapeRetainedFigureNineSourceTail
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteHeader
open PeriodicCNF.ClauseProfilePolarityRouteOperation
open HorizontalRoutedRouteHeader HorizontalRoutedRouteHeaderPresentationAtomScope
open PeriodicOrthocrossing OccurrenceSplitRing PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance atomRowCodesStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack

local instance atomRowCodesVariableDecidableEq : DecidableEq Variable := directSourceVariableDecidableEq

private theorem copiedRow_value (values : List Nat) (control : AtomScopeControl) :
    ({ literals := values, localFallback := values.getD 0 0 } : SourceOccurrenceAtomValueRow).value control =
      values.getD (HorizontalRoutedRouteHeaderCopiedSourcePosition.scopeOffset control) 0 := by
  cases control <;> rfl

theorem directSourceFinalCopiedInheritedRingAtomCodes_eq_value_blocks (symbols : List encoding.Γ) :
    directSourceFinalCopiedInheritedRingAtomCodes decider symbols =
      (directSourceFinalCopiedAtomValueBlocks decider symbols).flatMap
        (fun block => (clauseBlock block.1).map block.2.value) := by
  rw [directSourceFinalCopiedInheritedRingAtomCodes_eq_clause_blocks]
  simp only [directSourceFinalCopiedAtomValueBlocks, List.flatMap_map]
  apply List.flatMap_congr
  intro tagged _member
  apply List.map_congr_left
  intro control _controlMember
  exact (copiedRow_value _ control).symm

private theorem cycleRow_value
    (symbols : List encoding.Γ) (atom : WrappedPeriodicPlanarSATVariable Variable)
    (tagged : PositionedPeriodicClause RingVertex × Nat)
    (taggedMember : tagged ∈ PeriodicCNF.FormulaShapeFixedEightDirection.localCycleFormula.clauses.zipIdx)
    (control : AtomScopeControl)
    (controlMember : control ∈ clauseBlock (DirectedClauseProfile.ofClause cycleRoutes tagged.2 tagged.1)) :
    directSourceFinalInheritedRingCode decider symbols atom (directFinalCycleLiteralSlot tagged.1 control).val =
      ({ literals := tagged.1.literals.map
          (fun literal => directSourceFinalRingVariableCode decider symbols (ringCopy atom literal.atom)),
         localFallback := directSourceFinalInheritedRingCode decider symbols atom 0 } : SourceOccurrenceAtomValueRow).value control := by
  cases control with
  | parentLocal localControl => rfl
  | inherited slot =>
      have active := directFinalCycleLiteralSlot_inherited_active tagged taggedMember slot controlMember
      simp only [directFinalCycleLiteralSlot, List.getElem?_eq_getElem active,
        Option.map_some, Option.getD_some, SourceOccurrenceAtomValueRow.value]
      rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using active), List.getElem_map]
      exact (directSourceFinalRingVariableCode_ringCopy decider symbols atom _).symm

/-- The complete cycle column selects actual local literal values whenever
inherited, while preserving the compiler's own fallback at all other positions. -/
theorem directSourceFinalCycleInheritedRingAtomCodes_eq_value_blocks (symbols : List encoding.Γ) :
    directSourceFinalCycleInheritedRingAtomCodes decider symbols =
      (directSourceFinalCycleAtomValueBlocks decider symbols).flatMap
        (fun block => (clauseBlock block.1).map block.2.value) := by
  rw [directSourceFinalCycleInheritedRingAtomCodes_eq_actual_atoms,
    directSourceFinalLocalCycleRingVertexSlots_eq_literal_blocks]
  simp only [directSourceFinalCycleAtomValueBlocks, List.map_flatMap, List.map_map,
    List.flatMap_assoc, List.flatMap_map, Function.comp_def]
  apply List.flatMap_congr
  intro atom _atomMember
  apply List.flatMap_congr
  intro tagged taggedMember
  apply List.map_congr_left
  intro control controlMember
  exact cycleRow_value decider symbols atom tagged taggedMember control controlMember

theorem directSourceFinalInheritedRingAtomCodes_eq_value_blocks (symbols : List encoding.Γ) :
    directSourceFinalInheritedRingAtomCodes decider symbols =
      (directSourceFinalAtomValueBlocks decider symbols).flatMap
        (fun block => (clauseBlock block.1).map block.2.value) := by
  rw [directSourceFinalInheritedRingAtomCodes, directSourceFinalCopiedInheritedRingAtomCodes_eq_value_blocks,
    directSourceFinalCycleInheritedRingAtomCodes_eq_value_blocks, directSourceFinalAtomValueBlocks,
    List.flatMap_append]

/-- Every entry of the complete inherited-code stream is the value selected
by the corresponding coherent occurrence's own parent, profile, and header. -/
theorem directSourceFinalInheritedRingAtomCodes_eq_occurrence_rows (symbols : List encoding.Γ) :
    directSourceFinalInheritedRingAtomCodes decider symbols =
      (directSourceFinalOccurrences decider symbols).map
        (sourceOccurrenceAtomValue ((directSourceFinalAtomValueBlocks decider symbols).map Prod.snd)) := by
  rw [directSourceFinalInheritedRingAtomCodes_eq_value_blocks,
    ← sourceOccurrences_map_atomValueRows (directSourceFinalAtomValueBlocks decider symbols)
      (tailTables (directSourceFormula decider symbols))]
  unfold directSourceFinalOccurrences occurrences
  rw [directSourceFinalClauseDescriptors_eq_source_prefix, sourceOccurrences_append_variables,
    ← directSourceFinalAtomValueBlocks_profiles]

end LeanTrominoes.PeriodicCNFStripReduction

end
