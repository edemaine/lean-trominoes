/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationDirectionRequestHeaderPermutation
import LeanTrominoes.PeriodicThreeDMNormalizationTripleColorData
import LeanTrominoes.PeriodicThreeDMNormalizationVertexOrientation

/-! # Original-incidence data for retained-element request headers -/

namespace LeanTrominoes
namespace PeriodicThreeDM
namespace NormalizationDirectionRequest

open Gadget
open NormalizationCompiler

/-- Finite side/color data at the colored-element end of one original
incidence route. -/
def retainedIncidenceEndpointSideColor
    (input : NormalizationCompiler.Input) (color : WireColor)
    (incidence : Incidence) : EndpointSideColor :=
  (VertexSide.ofDirection
    (AxisDirection.polylineLastDirection
      (incidenceRoute input
        ⟨incidence.tripleIndex, color⟩)).opposite,
    color)

@[simp] theorem endpointSideColor_target_retained
    (input : NormalizationCompiler.Input) (color : WireColor)
    (atom : Nat) (incidence : Incidence) :
    endpointSideColor
        (input, .target (.retained color atom incidence)) =
      retainedIncidenceEndpointSideColor input color incidence := by
  rfl

/-- The three colored-element endpoint records in original incidence-list
order.  The fallback is irrelevant under the degree-three promise. -/
def retainedElementIncidenceTripleData
    (input : NormalizationCompiler.Input) (color : WireColor)
    (atom : Nat) : EndpointTripleData :=
  match input.problem.incidences color atom with
  | [first, second, third] =>
      (retainedIncidenceEndpointSideColor input color first,
        retainedIncidenceEndpointSideColor input color second,
        retainedIncidenceEndpointSideColor input color third)
  | _ =>
      ((.east, color), (.north, color), (.west, color))

/-- Canonical finite header data at one retained element endpoint. -/
def retainedElementEndpointHeaderData
    (input : NormalizationCompiler.Input) (color : WireColor)
    (atom : Nat) (incidence : Incidence) : EndpointHeaderData :=
  { vertexIsTriple := false
    fan := some (retainedElementIncidenceTripleData
      input color atom)
    endpoint := retainedIncidenceEndpointSideColor
      input color incidence }

/-- All choices at a retained monochromatic target can be read from the last
directions of its three original incidence routes. -/
theorem retainedElementTargetHeaderChoices_eq_incidenceData
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (degree : problem.DegreeTwoOrThree)
    (color : WireColor) (atom : Nat)
    (atomLt : atom < problem.elementCount color)
    (degreeThree : problem.degree color atom = 3)
    (incidence : Incidence) :
    let input := inputOfPresentation presentation.toPlanarPresentation
    let actual := endpointHeaderData input
      (.target (.retained color atom incidence))
    let canonical := retainedElementEndpointHeaderData
      input color atom incidence
    actual.firstChoice = canonical.firstChoice ∧
      actual.secondChoice = canonical.secondChoice ∧
      actual.finalChoice = canonical.finalChoice := by
  dsimp only
  obtain ⟨fan⟩ := exists_contractVertexFan_at_element
    presentation degree color atom atomLt degreeThree
  let input := inputOfPresentation presentation.toPlanarPresentation
  let endpoints : EndpointTriple :=
    (fan.first, fan.second, fan.third)
  let actualData := endpointTripleData (input, endpoints)
  let canonicalData := retainedElementIncidenceTripleData
    input color atom
  have incidenceLength :
      (problem.incidences color atom).length = 3 := by
    exact degreeThree
  obtain ⟨first, second, third, incidencesEq⟩ :=
    exists_eq_triple_of_length_eq_three
      (problem.incidences color atom) incidenceLength
  have inputIncidencesEq :
      input.problem.incidences color atom =
        [first, second, third] := by
    simpa [input, inputOfPresentation] using incidencesEq
  have dataAtEq :
      endpointTripleDataAt (input, .element color atom) =
        some actualData := by
    unfold endpointTripleDataAt endpointTripleAt
    dsimp [input]
    simp only [inputOfPresentation]
    rw [fan.endpoints_eq]
    rfl
  have targetPerm :=
    contractedEdgesForElement_targets_perm_endpointsAt
      problem degree color atom atomLt degreeThree
  rw [contractedEdgesForElement_of_incidences_triple
      problem color atom first second third incidencesEq,
    fan.endpoints_eq] at targetPerm
  have dataPerm :
      List.Perm (endpointTripleDataList canonicalData)
        (endpointTripleDataList actualData) := by
    have mapped := targetPerm.map
      (fun endpoint => endpointSideColor (input, endpoint))
    simpa [actualData, canonicalData, endpoints,
      endpointTripleDataList, endpointTripleData,
      retainedElementIncidenceTripleData,
      inputIncidencesEq] using mapped
  have sidesNodup :
      (endpointTripleDataList actualData).map Prod.fst |>.Nodup := by
    have firstEq : endpointSideColor (input, fan.first) =
        (fan.first.outwardSide presentation.toPlanarPresentation,
          fan.first.color) := by
      exact endpointSideColor_inputOfPresentation
        presentation.toPlanarPresentation fan.first
    have secondEq : endpointSideColor (input, fan.second) =
        (fan.second.outwardSide presentation.toPlanarPresentation,
          fan.second.color) := by
      exact endpointSideColor_inputOfPresentation
        presentation.toPlanarPresentation fan.second
    have thirdEq : endpointSideColor (input, fan.third) =
        (fan.third.outwardSide presentation.toPlanarPresentation,
          fan.third.color) := by
      exact endpointSideColor_inputOfPresentation
        presentation.toPlanarPresentation fan.third
    dsimp [actualData, endpoints, endpointTripleData,
      endpointTripleDataList]
    rw [firstEq, secondEq, thirdEq]
    exact fan.sidesNodup
  have headerDataEq :
      endpointHeaderData input
          (.target (.retained color atom incidence)) =
        (⟨false, some actualData,
          retainedIncidenceEndpointSideColor input color incidence⟩ :
            EndpointHeaderData) := by
    unfold endpointHeaderData
    change
      (⟨false,
        endpointTripleDataAt (input, .element color atom),
        endpointSideColor
          (input, .target (.retained color atom incidence))⟩ :
          EndpointHeaderData) = _
    rw [dataAtEq, endpointSideColor_target_retained]
  rw [show inputOfPresentation presentation.toPlanarPresentation = input
    by rfl]
  rw [headerDataEq]
  exact EndpointHeaderData.choices_eq_of_perm
    false actualData canonicalData
    (retainedIncidenceEndpointSideColor input color incidence)
    dataPerm sidesNodup

end NormalizationDirectionRequest
end PeriodicThreeDM
end LeanTrominoes
