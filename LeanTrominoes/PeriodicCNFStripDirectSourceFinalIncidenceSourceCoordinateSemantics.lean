/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalTripleCoordinateCompiler
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMVertexPositionAtComputed

/-! # Compiled incidence coordinates are actual drawing source positions -/

noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Computability Turing PeriodicCNF PeriodicOrthocrossing PeriodicThreeDM

private theorem map_range_getD {Value : Type} (values : List Value) (fallback : Value) :
    (List.range values.length).map (fun index => values.getD index fallback) = values := by
  apply List.ext_getElem
  · simp
  · intro index leftBound rightBound
    simp only [List.getElem_map, List.getElem_range]
    exact List.getD_eq_getElem values fallback rightBound

private theorem incidenceTags_map_positions (problem : PeriodicThreeDM)
    (positions : List Cell) (field : Cell → Nat)
    (aligned : problem.triples.length = positions.length) :
    problem.incidenceTags.map (fun tag => field (positions.getD tag.tripleIndex (0, 0))) =
      positions.flatMap (fun point => List.replicate 3 (field point)) := by
  rw [incidenceTags_eq_range_flatMap, aligned, List.map_flatMap]
  simp only [tripleIncidenceTags, List.map_map, Function.comp_def, List.map_const', incidenceColors]
  simpa only [List.flatMap_map, List.length_cons, List.length_nil] using congrArg
    (List.flatMap (fun point => List.replicate 3 (field point))) (map_range_getD positions (0, 0))

private theorem triplePositions_length_problem (source : PeriodicCNF Nat) :
    (horizontalThreeDMProblemComputed source).triples.length =
      (horizontalThreeDMTriplePositionsComputed source).length := by
  rw [← horizontalThreeDMPositionProblemComputed_eq]
  exact (horizontalThreeDMTriplePositionsComputed_length source).symm

/-- The numeric incidence tag selects its actual source triple in the drawing. -/
theorem horizontalIncidenceSourcePosition_eq_triplePosition
    (source : PeriodicCNF Nat) (tag : IncidenceTag)
    (member : tag ∈ (horizontalThreeDMProblemComputed source).incidenceTags) :
    (horizontalThreeDMDrawingComputed source).vertexPosition
        (horizontalThreeDMProblemComputed source).incidenceGraph (.triple tag.tripleIndex) =
      (horizontalThreeDMTriplePositionsComputed source).getD tag.tripleIndex (0, 0) := by
  have vertexMember : PeriodicThreeDMVertex.triple tag.tripleIndex ∈
      (horizontalThreeDMProblemComputed source).incidenceGraph.vertices := by
    change PeriodicThreeDMVertex.triple tag.tripleIndex ∈
      (horizontalThreeDMProblemComputed source).tripleVertices ++
        (horizontalThreeDMProblemComputed source).elementVertices
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨tag.tripleIndex,
      List.mem_range.mpr (incidenceTag_tripleIndex_lt _ member), rfl⟩
  rw [horizontalThreeDMDrawingComputed_vertexPosition_eq_positionAt source vertexMember]
  rfl

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- RGB coordinate copies agree with the actual drawing at every canonical
incidence tag, in exactly the order used by incidence identities and directions. -/
theorem directSourceFinalIncidenceSourceCoordinates_eq_drawing
    (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    directSourceFinalIncidenceSourceCoordinates decider horizontal keepPositive symbols =
      (horizontalThreeDMProblemComputed (PolySpaceCompiler.formulaOfSymbols decider symbols)).incidenceTags.map
        (fun tag => CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal keepPositive)
          ((horizontalThreeDMDrawingComputed (PolySpaceCompiler.formulaOfSymbols decider symbols)).vertexPosition
            (horizontalThreeDMProblemComputed (PolySpaceCompiler.formulaOfSymbols decider symbols)).incidenceGraph
              (.triple tag.tripleIndex))) := by
  rw [directSourceFinalIncidenceSourceCoordinates_eq_horizontal,
    ← incidenceTags_map_positions _ _ _ (triplePositions_length_problem _)]
  apply List.map_congr_left
  intro tag member
  rw [horizontalIncidenceSourcePosition_eq_triplePosition _ tag member]

@[simp] theorem directSourceFinalIncidenceSourceCoordinates_length
    (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    (directSourceFinalIncidenceSourceCoordinates decider horizontal keepPositive symbols).length =
      (horizontalThreeDMProblemComputed (PolySpaceCompiler.formulaOfSymbols decider symbols)).incidenceTags.length := by
  rw [directSourceFinalIncidenceSourceCoordinates_eq_drawing, List.length_map]

noncomputable def directSourceFinalDrawingIncidenceSourceCoordinatesComputableInPolyTime
    (horizontal keepPositive : Bool) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (fun symbols =>
        (horizontalThreeDMProblemComputed (PolySpaceCompiler.formulaOfSymbols decider symbols)).incidenceTags.map
          (fun tag => CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal keepPositive)
            ((horizontalThreeDMDrawingComputed (PolySpaceCompiler.formulaOfSymbols decider symbols)).vertexPosition
              (horizontalThreeDMProblemComputed (PolySpaceCompiler.formulaOfSymbols decider symbols)).incidenceGraph
                (.triple tag.tripleIndex)))) :=
  TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (directSourceFinalIncidenceSourceCoordinatesComputableInPolyTime decider horizontal keepPositive)
    (fun symbols => congrArg UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalIncidenceSourceCoordinates_eq_drawing decider horizontal keepPositive symbols))

end LeanTrominoes.PeriodicCNFStripReduction
end
