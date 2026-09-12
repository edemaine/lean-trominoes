/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalSourceOccurrenceParentIndices
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseOriginCompiler
import LeanTrominoes.UnaryIndexedValueLookupSemantics

/-! # Compiled source-parent clause origins in final occurrence order -/

noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Computability Turing PeriodicCNF PeriodicOrthocrossing
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteTail
open PeriodicCNF.FormulaShapeRetainedFigureNineSourceTail

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance occurrenceOriginStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack
attribute [local instance] directSourceVariableDecidableEqInstance

/-- Original pre-Figure 9 parent indices, including copied and cycle parents. -/
def directSourceFinalSourceParentIndices (symbols : List encoding.Γ) : List Nat :=
  HorizontalRoutedRouteHeaderCopiedParentIndex.parentIndices (directSourceFinalClauseDescriptors decider symbols)

noncomputable def directSourceFinalSourceParentIndicesComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields (directSourceFinalSourceParentIndices decider) := by
  unfold directSourceFinalSourceParentIndices
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalClauseDescriptorsComputableInPolyTime decider)
    HorizontalRoutedRouteHeaderCopiedParentIndex.parentIndicesComputableInPolyTime

@[simp] theorem directSourceFinalSourceParentIndices_length (symbols : List encoding.Γ) :
    (directSourceFinalSourceParentIndices decider symbols).length =
      (directSourceFinalCompiledOccurrenceData decider symbols).length := by
  rw [directSourceFinalSourceParentIndices, HorizontalRoutedRouteHeaderCopiedParentIndex.parentIndices_length,
    directSourceFinalClauseDescriptors_occurrenceData_eq]

theorem directSourceFinalSourceParentIndices_eq_occurrences (symbols : List encoding.Γ) :
    directSourceFinalSourceParentIndices decider symbols =
      (directSourceFinalOccurrences decider symbols).map SourceOccurrence.parentClauseIndex := by
  rw [directSourceFinalSourceParentIndices,
    HorizontalRoutedRouteHeaderCopiedParentIndex.parentIndices_eq_sourceOccurrences _ (tailTables (directSourceFormula decider symbols))]
  unfold directSourceFinalOccurrences occurrences
  rw [directSourceFinalClauseDescriptors_eq_source_prefix, sourceOccurrences_append_variables]

/-- Every compiled source-parent index has an actual clause lookup. -/
theorem directSourceFinalSourceParentIndices_lt (symbols : List encoding.Γ) (parent : Nat)
    (member : parent ∈ directSourceFinalSourceParentIndices decider symbols) :
    parent < (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
      (directSourceFormula decider symbols)).clauses.length := by
  rw [directSourceFinalSourceParentIndices_eq_occurrences] at member
  obtain ⟨occurrence, occurrenceMember, rfl⟩ := List.mem_map.mp member
  obtain ⟨witness⟩ := occurrenceWitness (directSourceFormula decider symbols)
    (sourceFormula_widthAtMostThree (PolySpaceCompiler.formulaOfSymbols decider symbols))
    (sourceFormula_clausesNonempty (PolySpaceCompiler.formulaOfSymbols decider symbols)) occurrence occurrenceMember
  exact (List.getElem?_eq_some_iff.mp witness.sourceLookup).1

/-- Broadcast each stored parent origin to all of its final occurrence rows. -/
def directSourceFinalOccurrenceClauseOrigins (horizontal keepPositive : Bool) (symbols : List encoding.Γ) : List Nat :=
  UnaryIndexedValueLookup.values (directSourceFinalSourceParentIndices decider symbols)
    (directSourceFinalClauseOrigins decider horizontal keepPositive symbols)

noncomputable def directSourceFinalOccurrenceClauseOriginsComputableInPolyTime (horizontal keepPositive : Bool) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalOccurrenceClauseOrigins decider horizontal keepPositive) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ := ⟨Classical.choice nonemptyAlphabet⟩
    unfold directSourceFinalOccurrenceClauseOrigins
    exact UnaryIndexedValueLookup.valuesComputableInPolyTime id
      (directSourceFinalSourceParentIndices decider) (directSourceFinalClauseOrigins decider horizontal keepPositive)
      (directSourceFinalSourceParentIndicesComputableInPolyTime decider)
      (directSourceFinalClauseOriginsComputableInPolyTime decider horizontal keepPositive)
  else by
    letI : IsEmpty encoding.Γ := ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime UnaryFieldEncoderMachine.unaryFields _

@[simp] theorem directSourceFinalOccurrenceClauseOrigins_length (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    (directSourceFinalOccurrenceClauseOrigins decider horizontal keepPositive symbols).length =
      (directSourceFinalCompiledOccurrenceData decider symbols).length := by
  rw [directSourceFinalOccurrenceClauseOrigins, UnaryIndexedValueLookup.values_length, directSourceFinalSourceParentIndices_length]

theorem directSourceFinalOccurrenceClauseOrigins_eq_occurrence_rows (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    directSourceFinalOccurrenceClauseOrigins decider horizontal keepPositive symbols =
      (directSourceFinalOccurrences decider symbols).map fun occurrence =>
        (directSourceFinalClauseOrigins decider horizontal keepPositive symbols).getD occurrence.parentClauseIndex 0 := by
  unfold directSourceFinalOccurrenceClauseOrigins
  rw [UnaryIndexedValueLookup.values_eq_map_getD_of_forall_lt _ _ (by
    intro parent member
    rw [directSourceFinalClauseOrigins_length]
    exact directSourceFinalSourceParentIndices_lt decider symbols parent member),
    directSourceFinalSourceParentIndices_eq_occurrences, List.map_map]
  simp only [Function.comp_def]

/-- At an actual occurrence, the emitted field is its own parent's stored
coordinate, with no fallback or independently reconstructed provenance. -/
theorem directSourceFinalOccurrenceClauseOrigins_lookup (horizontal keepPositive : Bool) (symbols : List encoding.Γ)
    (index : Nat) (occurrence : SourceOccurrence)
    (lookup : (directSourceFinalOccurrences decider symbols)[index]? = some occurrence)
    (witness : OccurrenceWitness (directSourceFormula decider symbols) occurrence) :
    (directSourceFinalOccurrenceClauseOrigins decider horizontal keepPositive symbols)[index]? =
      some (CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal keepPositive) witness.refinedClause.position) := by
  rw [directSourceFinalOccurrenceClauseOrigins_eq_occurrence_rows, List.getElem?_map, lookup, Option.map_some,
    directSourceFinalClauseOrigins_eq_stored_positions, List.getD_eq_getElem?_getD,
    List.getElem?_map, witness.sourceLookup]
  rfl

end LeanTrominoes.PeriodicCNFStripReduction
end
