/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGadgetOriginCoordinateCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedOccurrenceEntryOrder
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedParentIndexCompiler
import LeanTrominoes.PeriodicCNFStripHorizontalNormalizedAtomOccurrences

/-! # Actual variable gadget origins in canonical occurrence-entry order -/

noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Computability Turing PeriodicCNF PeriodicOrthocrossing
open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  sourceVariableDecidableEq
  horizontalRibbonInnerVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance groupedOriginStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack

/-- Reuse the canonical occurrence queries for all four signed origin columns. -/
def directSourceFinalGroupedVariableOriginCoordinates
    (horizontal keepPositive : Bool) (symbols : List encoding.Γ) : List Nat :=
  UnaryIndexedValueLookup.values
    (directSourceFinalGroupedOccurrenceIndices decider symbols)
    (directSourceFinalGadgetOriginCoordinates decider true horizontal keepPositive symbols)

noncomputable def directSourceFinalGroupedVariableOriginCoordinatesComputableInPolyTime
    (horizontal keepPositive : Bool) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalGroupedVariableOriginCoordinates decider horizontal keepPositive) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ := ⟨Classical.choice nonemptyAlphabet⟩
    unfold directSourceFinalGroupedVariableOriginCoordinates
    exact UnaryIndexedValueLookup.valuesComputableInPolyTime id _ _
      (directSourceFinalGroupedOccurrenceIndicesComputableInPolyTime decider)
      (directSourceFinalGadgetOriginCoordinatesComputableInPolyTime decider true horizontal keepPositive)
  else by
    letI : IsEmpty encoding.Γ := ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime
      UnaryFieldEncoderMachine.unaryFields _

@[simp] theorem directSourceFinalGroupedVariableOriginCoordinates_length
    (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    (directSourceFinalGroupedVariableOriginCoordinates decider horizontal keepPositive symbols).length =
      (directSourceFinalGroupedOccurrenceIndices decider symbols).length := by
  exact UnaryIndexedValueLookup.values_length _ _

private theorem originCoordinates_length
    (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    (directSourceFinalGadgetOriginCoordinates decider true horizontal keepPositive symbols).length =
      (directSourceFinalCompiledOccurrenceData decider symbols).length := by
  rw [directSourceFinalGadgetOriginCoordinates_eq_affine, List.length_map,
    directSourceFinalRoutedVertexPoints_length]

/-- Every queried origin belongs to the same actual atom as its grouped fan
and slot fields. Repeated active slots retain their common gadget origin. -/
theorem directSourceFinalGroupedVariableOriginCoordinates_eq_horizontal
    (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    directSourceFinalGroupedVariableOriginCoordinates decider horizontal keepPositive symbols =
      (occurrenceEntries (horizontalSemanticNormalizedRibbonSource
        (PolySpaceCompiler.formulaOfSymbols decider symbols)).erase).map
        (fun entry => CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal keepPositive)
          (horizontalThreeDMVariableOriginComputed (PolySpaceCompiler.formulaOfSymbols decider symbols) entry.1)) := by
  unfold directSourceFinalGroupedVariableOriginCoordinates
  rw [UnaryIndexedValueLookup.values_eq_map_getD_of_forall_lt _ _ (fun index member => by
    rw [originCoordinates_length]
    exact directSourceFinalGroupedOccurrenceIndex_lt decider symbols index member)]
  rw [directSourceFinalGroupedOccurrenceIndices_eq_occurrenceEntries,
    directSourceFinalGadgetOriginCoordinates_eq_horizontal,
    directSourceFinalHorizontalGadgetOriginCoordinates,
    directSourceFinalHorizontalGadgetOrigins]
  simp only [↓reduceIte, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro entry member
  have lookup := (occurrenceEntryIndex_spec (horizontalSemanticNormalizedRibbonSource
    (PolySpaceCompiler.formulaOfSymbols decider symbols)).erase entry member).1
  rw [horizontalSemanticNormalizedRibbonSource_variableOccurrences] at lookup
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, lookup,
    Option.map_some, Option.getD_some]

end LeanTrominoes.PeriodicCNFStripReduction
end
