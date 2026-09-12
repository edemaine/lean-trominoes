/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalPolarityClauseCoordinateSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOriginalAtomHorizontalSemantics
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedPlacementBridge

/-! # Complete compiled clause coordinates agree with the horizontal source -/

noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Computability Turing PeriodicCNF PeriodicOrthocrossing
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteTail
open PeriodicCNF.FormulaShapeRetainedFigureNineSourceTail
open PeriodicOneInThreePolarityNormalizationRouteSubdivision

private theorem eq_map_of_pointwise_lookup {Source Target : Type}
    (source : List Source) (values : List Target) (value : Source → Target)
    (lengths : values.length = source.length)
    (lookup : ∀ (index : Nat) (atom : Source), source[index]? = some atom → values[index]? = some (value atom)) :
    values = source.map value := by
  apply List.ext_getElem?
  intro index
  rw [List.getElem?_map]
  cases selected : source[index]? with
  | none =>
      simp only [Option.map_none]
      apply List.getElem?_eq_none_iff.mpr
      rw [lengths]
      exact List.getElem?_eq_none_iff.mp selected
  | some atom =>
      simp only [Option.map_some]
      exact lookup index atom selected

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance horizontalClauseCoordinateStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack
attribute [local instance] directSourceVariableDecidableEqInstance

/-- Coherent source occurrences and exact semantic metadata have identical
source indices and polarity operations in the complete output order. -/
theorem directSourceFinalOccurrences_map_descriptor_eq_exactMetadata (symbols : List encoding.Γ) :
    (directSourceFinalOccurrences decider symbols).map sourceOccurrencePolarityDescriptor =
      (directSourceFinalExactMetadataRouteBlocks decider symbols).map RouteDirectionBlock.sourceIndexedDescriptor := by
  have identified := directFigureNinePolarityRoutePairs_sourceIndexedDescriptor_eq_exactMetadata decider symbols
  rw [← directSourceFinalOccurrences_map_generatedClauseIndex,
    ← directSourceFinalOccurrences_map_pair, List.zipWith_map, List.zipWith_self] at identified
  unfold sourceOccurrencePolarityDescriptor
  simpa only [SourceOccurrence.pair] using identified

/-- Descriptor clause positions are the actual canonical origins of all
horizontal output incidences. -/
theorem directSourceFinalOccurrences_map_clausePosition_eq_horizontal (symbols : List encoding.Γ) :
    (directSourceFinalOccurrences decider symbols).map
      (fun occurrence => (sourceOccurrencePolarityDescriptor occurrence).clausePosition
        (refinedSource (directSourceFinalGaugedFormula decider symbols)
          (directSourceFinalGaugedPlacement decider symbols))
        (directSourceFinalGaugedIncidenceRoutes decider symbols)) =
      presentedIncidenceClausePositions
        (horizontalRoutedFormulaComputed (PolySpaceCompiler.formulaOfSymbols decider symbols))
        (horizontalRoutedPlacementComputed (PolySpaceCompiler.formulaOfSymbols decider symbols)) := by
  have identified := congrArg (List.map (fun descriptor : SourceIndexedDescriptor =>
    descriptor.clausePosition
      (refinedSource (directSourceFinalGaugedFormula decider symbols)
        (directSourceFinalGaugedPlacement decider symbols))
      (directSourceFinalGaugedIncidenceRoutes decider symbols)))
    (directSourceFinalOccurrences_map_descriptor_eq_exactMetadata decider symbols)
  simp only [List.map_map, Function.comp_def] at identified
  rw [directSourceFinalExactMetadataRouteBlocks, exactMetadataRouteBlocks_map_clausePosition] at identified
  have formulaEq : formula (directSourceFinalGaugedFormula decider symbols)
      (directSourceFinalGaugedPlacement decider symbols) (directSourceFinalGaugedIncidenceRoutes decider symbols) =
      horizontalRoutedFormulaComputed (PolySpaceCompiler.formulaOfSymbols decider symbols) := by
    rw [horizontalRoutedFormulaComputed_eq_semantic]
    unfold directSourceFinalGaugedFormula directSourceFinalClockwiseFormula
      directSourceFinalGaugedPlacement directSourceFinalGaugedIncidenceRoutes directSourceFormula
    rfl
  have placementEq : placement (directSourceFinalGaugedPlacement decider symbols)
      (directSourceFinalGaugedIncidenceRoutes decider symbols) =
      horizontalRoutedPlacementComputed (PolySpaceCompiler.formulaOfSymbols decider symbols) := by
    rw [horizontalRoutedPlacementComputed_eq_semantic]
    unfold directSourceFinalGaugedPlacement directSourceFinalGaugedIncidenceRoutes directSourceFormula
    rfl
  rw [← formulaEq, ← placementEq]
  exact identified

/-- Exact scalar fields of every actual horizontal canonical clause origin,
repeated in clause-major, literal-minor order. -/
def directSourceFinalHorizontalClauseCoordinates (horizontal keepPositive : Bool) (symbols : List encoding.Γ) : List Nat :=
  (presentedIncidenceClausePositions
    (horizontalRoutedFormulaComputed (PolySpaceCompiler.formulaOfSymbols decider symbols))
    (horizontalRoutedPlacementComputed (PolySpaceCompiler.formulaOfSymbols decider symbols))).map
      (CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal keepPositive))

/-- The single affine compiler emits all actual horizontal clause positions,
with source promises and decoder validity discharged. -/
theorem directSourceFinalPolarityClauseCoordinates_eq_horizontal
    (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    directSourceFinalPolarityClauseCoordinates decider horizontal keepPositive symbols =
      directSourceFinalHorizontalClauseCoordinates decider horizontal keepPositive symbols := by
  let value := fun occurrence : SourceOccurrence =>
    CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal keepPositive)
      ((sourceOccurrencePolarityDescriptor occurrence).clausePosition
        (refinedSource (directSourceFinalGaugedFormula decider symbols)
          (directSourceFinalGaugedPlacement decider symbols))
        (directSourceFinalGaugedIncidenceRoutes decider symbols))
  have coordinates : directSourceFinalPolarityClauseCoordinates decider horizontal keepPositive symbols =
      (directSourceFinalOccurrences decider symbols).map value := by
    apply eq_map_of_pointwise_lookup
    · rw [directSourceFinalPolarityClauseCoordinates_length, directSourceFinalOccurrences_length_eq_compiled]
    · intro index occurrence lookup
      have indexLt := (List.getElem?_eq_some_iff.mp lookup).1
      have witness : OccurrenceWitness (directSourceFormula decider symbols) occurrence := by
        have chosen := directSourceFinalOccurrenceWitness decider symbols index indexLt
        rw [(List.getElem?_eq_some_iff.mp lookup).2] at chosen
        exact chosen
      have decodedMember : (sourceOccurrencePolarityDescriptor occurrence).atom?
          (refinedSource (directSourceFinalGaugedFormula decider symbols)
            (directSourceFinalGaugedPlacement decider symbols)).erase ∈
          (horizontalRoutedFormulaComputed (PolySpaceCompiler.formulaOfSymbols decider symbols)).erase.variableOccurrences.map some := by
        rw [← directSourceFinalOccurrences_map_atom_eq_horizontal decider symbols]
        exact List.mem_map.mpr ⟨occurrence, List.mem_iff_getElem?.mpr ⟨index, lookup⟩, rfl⟩
      obtain ⟨atom, _, decoded⟩ := List.mem_map.mp decodedMember
      have sourceLocal : (directSourceFormula decider symbols).IsLocal :=
        sourceFormula_isLocal (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)
      have sourceWidth : (directSourceFormula decider symbols).WidthAtMost 3 :=
        sourceFormula_widthAtMostThree (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)
      have sourceOccurrences : @PeriodicCNF.OccurrencesAtMost Variable
          (@instBEqOfDecidableEq Variable directSourceVariableDecidableEqInstance) (by infer_instance) 3
          (directSourceFormula decider symbols) :=
        PeriodicCNF.occurrencesAtMost_congr_beq _ _ (by infer_instance) (by infer_instance) 3 _
          (sourceFormula_occurrencesAtMostThree (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols))
      have sourceNonempty : ∀ clause ∈ (directSourceFormula decider symbols).clauses, clause ≠ [] :=
        sourceFormula_clausesNonempty (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)
      have coordinate := directSourceFinalPolarityClauseCoordinates_descriptor_lookup decider horizontal keepPositive symbols
        sourceLocal sourceWidth sourceOccurrences sourceNonempty index occurrence lookup witness atom
        (by simpa only [sourceOccurrencePolarityDescriptor, directSourceFinalGaugedFormula,
          directSourceFinalClockwiseFormula, directSourceFinalGaugedPlacement,
          retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula] using decoded.symm)
      simpa only [value, sourceOccurrencePolarityDescriptor, directSourceFinalGaugedFormula,
        directSourceFinalClockwiseFormula, directSourceFinalGaugedPlacement, directSourceFinalGaugedIncidenceRoutes,
        retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula] using coordinate
  rw [coordinates]
  unfold directSourceFinalHorizontalClauseCoordinates
  rw [← directSourceFinalOccurrences_map_clausePosition_eq_horizontal decider symbols, List.map_map]
  rfl

/-- Native polynomial-time emission of the actual horizontal clause-coordinate
column, including the case of an empty input alphabet. -/
noncomputable def directSourceFinalHorizontalClauseCoordinatesComputableInPolyTime (horizontal keepPositive : Bool) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalHorizontalClauseCoordinates decider horizontal keepPositive) := by
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (directSourceFinalPolarityClauseCoordinatesComputableInPolyTime decider horizontal keepPositive)
    (fun symbols => congrArg UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalPolarityClauseCoordinates_eq_horizontal decider horizontal keepPositive symbols))

end LeanTrominoes.PeriodicCNFStripReduction
end
