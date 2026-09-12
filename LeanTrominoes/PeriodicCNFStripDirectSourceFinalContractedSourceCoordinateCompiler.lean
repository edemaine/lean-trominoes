/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalIncidenceValueSelection
import LeanTrominoes.PeriodicCNFStripCountedContractedIncidenceSourceFilter
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalIncidenceSourceCoordinateSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCanonicalElementDegreeHorizontalSemantics
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMProblemSemanticBridge

/-! # Actual contracted-route starting coordinates from direct source symbols -/

noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Computability Turing PeriodicCNF PeriodicOrthocrossing PeriodicThreeDM

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- Regroup incidence coordinates by element and retain exactly the source
incidence of each contracted edge. -/
def directSourceFinalContractedSourceCoordinates (horizontal keepPositive : Bool)
    (symbols : List encoding.Γ) : List Nat :=
  UnaryFieldBooleanFilter.selectedValues
    (CountedContractedIncidence.sourceControls (directSourceFinalCanonicalElementDegrees decider symbols))
    (directSourceFinalSelectedIncidenceValues decider symbols
      (directSourceFinalIncidenceSourceCoordinates decider horizontal keepPositive symbols))

noncomputable def directSourceFinalContractedSourceCoordinatesComputableInPolyTime
    (horizontal keepPositive : Bool) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalContractedSourceCoordinates decider horizontal keepPositive) := by
  unfold directSourceFinalContractedSourceCoordinates
  exact UnaryFieldBooleanFilter.selectedValuesNativeListComputableInPolyTime _ _
    (TM2CompositionMachine.computableInPolyTime
      (directSourceFinalCanonicalElementDegreesComputableInPolyTime decider)
      CountedContractedIncidence.sourceControlsComputableInPolyTime)
    (directSourceFinalSelectedIncidenceValuesComputableInPolyTime decider _
      (directSourceFinalIncidenceSourceCoordinates_length decider horizontal keepPositive)
      (directSourceFinalIncidenceSourceCoordinatesComputableInPolyTime decider horizontal keepPositive))

/-- Exact starting positions of the actual contracted routes, including
retained edges and the first incidence of every through edge. -/
theorem directSourceFinalContractedSourceCoordinates_eq_horizontal
    (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    directSourceFinalContractedSourceCoordinates decider horizontal keepPositive symbols =
      (horizontalThreeDMProblemComputed (PolySpaceCompiler.formulaOfSymbols decider symbols)).contractedEdges.map
        (fun edge => CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal keepPositive)
          ((horizontalThreeDMDrawingComputed (PolySpaceCompiler.formulaOfSymbols decider symbols)).vertexPosition
            (horizontalThreeDMProblemComputed (PolySpaceCompiler.formulaOfSymbols decider symbols)).incidenceGraph
              edge.toPeriodicEdge.source)) := by
  unfold directSourceFinalContractedSourceCoordinates
  rw [directSourceFinalIncidenceSourceCoordinates_eq_drawing,
    directSourceFinalSelectedIncidenceValues_map_eq_horizontal,
    directSourceFinalCanonicalElementDegrees_eq_horizontal,
    CountedContractedIncidence.selected_sources_eq_contracted
      (horizontalThreeDMProblemComputed (PolySpaceCompiler.formulaOfSymbols decider symbols))
      (fun tag : IncidenceTag => CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal keepPositive)
        ((horizontalThreeDMDrawingComputed (PolySpaceCompiler.formulaOfSymbols decider symbols)).vertexPosition
          (horizontalThreeDMProblemComputed (PolySpaceCompiler.formulaOfSymbols decider symbols)).incidenceGraph
            (.triple tag.tripleIndex))) (by
      rw [horizontalThreeDMProblemComputed_eq_problem]
      exact problem_degreeTwoOrThree _)]
  apply List.map_congr_left
  intro edge _
  cases edge <;> rfl

@[simp] theorem directSourceFinalContractedSourceCoordinates_length
    (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    (directSourceFinalContractedSourceCoordinates decider horizontal keepPositive symbols).length =
      (horizontalThreeDMProblemComputed (PolySpaceCompiler.formulaOfSymbols decider symbols)).contractedEdges.length := by
  rw [directSourceFinalContractedSourceCoordinates_eq_horizontal, List.length_map]

/-- An unconditional native compiler for each signed coordinate column of
the actual route starts used by raster metadata. -/
noncomputable def directSourceFinalHorizontalContractedSourceCoordinatesComputableInPolyTime
    (horizontal keepPositive : Bool) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (fun symbols =>
        (horizontalThreeDMProblemComputed (PolySpaceCompiler.formulaOfSymbols decider symbols)).contractedEdges.map
          (fun edge => CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal keepPositive)
            ((horizontalThreeDMDrawingComputed (PolySpaceCompiler.formulaOfSymbols decider symbols)).vertexPosition
              (horizontalThreeDMProblemComputed (PolySpaceCompiler.formulaOfSymbols decider symbols)).incidenceGraph
                edge.toPeriodicEdge.source))) :=
  TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (directSourceFinalContractedSourceCoordinatesComputableInPolyTime decider horizontal keepPositive)
    (fun symbols => congrArg UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalContractedSourceCoordinates_eq_horizontal decider horizontal keepPositive symbols))

end LeanTrominoes.PeriodicCNFStripReduction
end
