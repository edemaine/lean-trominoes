/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationStripReverseElementVertex

/-!
# Colored-element constraints read from normalized strip orientations
-/

namespace LeanTrominoes

open Gadget

namespace PeriodicThreeDM

set_option maxRecDepth 2048

/-- A degree-two colored element satisfies the extracted suppressed wire
constraint. -/
theorem ContinuousPlanarPresentation.reverseStripGraphOrientation_element_degreeTwo
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (horizontal : problem.IsOneDimensional)
    (sourceInside :
      presentation.toPlanarPresentation.drawing
        |>.RoutePointsInExpandedVerticalBand)
    (collisionFree :
      presentation.toPlanarPresentation.FinalStripAssignmentsCollisionFree)
    (orientation :
      presentation.toPlanarPresentation.stripNormalizedOrthogonalDrawing
        |>.Orientation)
    (valid :
      presentation.toPlanarPresentation.stripNormalizedOrthogonalDrawing
        |>.IsOrientation orientation)
    (color : WireColor) (atom : Nat)
    (atomLt : atom < problem.elementCount color)
    (degreeTwo : problem.degree color atom = 2)
    (translate : Cell) :
    SuppressedElementConstraint
      (problem.graphIncidentValues
        (presentation.toPlanarPresentation.reverseStripGraphOrientation
          orientation) color atom translate) := by
  obtain ⟨first, second, incidences⟩ :
      ∃ first second, problem.incidences color atom = [first, second] := by
    unfold PeriodicThreeDM.degree at degreeTwo
    generalize incidenceListEq :
      problem.incidences color atom = incidenceList at degreeTwo ⊢
    change incidenceList.length = 2 at degreeTwo
    rcases incidenceList with _ | ⟨first, incidenceList⟩
    · simp at degreeTwo
    rcases incidenceList with _ | ⟨second, incidenceList⟩
    · simp at degreeTwo
    rcases incidenceList with _ | ⟨third, incidenceList⟩
    · exact ⟨first, second, rfl⟩
    · simp at degreeTwo
  let edge := ContractedEdge.through color atom first second
  have localEdgeMember : edge ∈
      problem.contractedEdgesForElement color atom := by
    rw [contractedEdgesForElement_of_incidences_pair
      problem color atom first second incidences]
    simp [edge]
  have edgeMember := contractedEdgesForElement_mem_contractedEdges
    problem color atom atomLt localEdgeMember
  let sourceTranslate := Cell.sub translate first.offset
  have targetTranslate :
      Cell.add sourceTranslate (Cell.sub first.offset second.offset) =
        Cell.sub translate second.offset := by
    rcases translate with ⟨translateX, translateY⟩
    rcases first with ⟨firstIndex, firstX, firstY⟩
    rcases second with ⟨secondIndex, secondX, secondY⟩
    simp [sourceTranslate, Cell.add, Cell.sub]
  have different := presentation.reverseStripGraphOrientation_through_ne
    wellFormed degree horizontal sourceInside collisionFree orientation valid
      color atom first second edgeMember sourceTranslate
  rw [graphIncidentValues, incidences]
  simp only [List.map_cons, List.map_nil,
    suppressedElementConstraint_pair_iff]
  simpa [edge, ContractedEdge.sourceTag, ContractedEdge.targetTag,
    sourceTranslate, targetTranslate] using different

/-- A retained degree-three colored element satisfies its extracted exact-one
constraint. -/
theorem ContinuousPlanarPresentation.reverseStripGraphOrientation_element_degreeThree
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (horizontal : problem.IsOneDimensional)
    (sourceInside :
      presentation.toPlanarPresentation.drawing
        |>.RoutePointsInExpandedVerticalBand)
    (collisionFree :
      presentation.toPlanarPresentation.FinalStripAssignmentsCollisionFree)
    (orientation :
      presentation.toPlanarPresentation.stripNormalizedOrthogonalDrawing
        |>.Orientation)
    (valid :
      presentation.toPlanarPresentation.stripNormalizedOrthogonalDrawing
        |>.IsOrientation orientation)
    (color : WireColor) (atom : Nat)
    (atomLt : atom < problem.elementCount color)
    (degreeThree : problem.degree color atom = 3)
    (translate : Cell) :
    SuppressedElementConstraint
      (problem.graphIncidentValues
        (presentation.toPlanarPresentation.reverseStripGraphOrientation
          orientation) color atom translate) := by
  obtain ⟨first, second, third, incidences⟩ :
      ∃ first second third,
        problem.incidences color atom = [first, second, third] := by
    unfold PeriodicThreeDM.degree at degreeThree
    generalize incidenceListEq :
      problem.incidences color atom = incidenceList at degreeThree ⊢
    change incidenceList.length = 3 at degreeThree
    rcases incidenceList with _ | ⟨first, incidenceList⟩
    · simp at degreeThree
    rcases incidenceList with _ | ⟨second, incidenceList⟩
    · simp at degreeThree
    rcases incidenceList with _ | ⟨third, incidenceList⟩
    · simp at degreeThree
    rcases incidenceList with _ | ⟨fourth, incidenceList⟩
    · exact ⟨first, second, third, rfl⟩
    · simp at degreeThree
  let firstEdge := ContractedEdge.retained color atom first
  let secondEdge := ContractedEdge.retained color atom second
  let thirdEdge := ContractedEdge.retained color atom third
  have firstLocal : firstEdge ∈
      problem.contractedEdgesForElement color atom := by
    rw [contractedEdgesForElement_of_incidences_triple
      problem color atom first second third incidences]
    simp [firstEdge]
  have secondLocal : secondEdge ∈
      problem.contractedEdgesForElement color atom := by
    rw [contractedEdgesForElement_of_incidences_triple
      problem color atom first second third incidences]
    simp [secondEdge]
  have thirdLocal : thirdEdge ∈
      problem.contractedEdgesForElement color atom := by
    rw [contractedEdgesForElement_of_incidences_triple
      problem color atom first second third incidences]
    simp [thirdEdge]
  have firstMember := contractedEdgesForElement_mem_contractedEdges
    problem color atom atomLt firstLocal
  have secondMember := contractedEdgesForElement_mem_contractedEdges
    problem color atom atomLt secondLocal
  have thirdMember := contractedEdgesForElement_mem_contractedEdges
    problem color atom atomLt thirdLocal
  have firstValue := presentation.reverseStripGraphOrientation_retained_eq_target
    wellFormed degree horizontal sourceInside collisionFree orientation valid
      color atom first firstMember (Cell.sub translate first.offset)
  have secondValue := presentation.reverseStripGraphOrientation_retained_eq_target
    wellFormed degree horizontal sourceInside collisionFree orientation valid
      color atom second secondMember (Cell.sub translate second.offset)
  have thirdValue := presentation.reverseStripGraphOrientation_retained_eq_target
    wellFormed degree horizontal sourceInside collisionFree orientation valid
      color atom third thirdMember (Cell.sub translate third.offset)
  have endpointExactlyOne :=
    presentation.retainedStripElementDrawingInwardValues_exactlyOne
      wellFormed degree horizontal sourceInside collisionFree orientation valid
        color atom atomLt degreeThree translate
  rw [graphIncidentValues, incidences]
  simp only [List.map_cons, List.map_nil,
    suppressedElementConstraint_triple_iff]
  unfold PlanarPresentation.retainedStripElementDrawingInwardValues at endpointExactlyOne
  rw [contractedEdgesForElement_of_incidences_triple
    problem color atom first second third incidences] at endpointExactlyOne
  simp only [List.map_cons, List.map_nil] at endpointExactlyOne
  rw [Cell.add_sub_right_cancel] at firstValue secondValue thirdValue
  dsimp only at firstValue secondValue thirdValue
  have firstValue' :
      presentation.toPlanarPresentation.reverseStripGraphOrientation orientation
          ⟨first.tripleIndex, color⟩ (Cell.sub translate first.offset) =
        presentation.toPlanarPresentation.stripDrawingEndpointInward orientation
          (.target firstEdge) translate := by
    simpa [firstEdge, ContractedEdge.sourceTag] using firstValue
  have secondValue' :
      presentation.toPlanarPresentation.reverseStripGraphOrientation orientation
          ⟨second.tripleIndex, color⟩ (Cell.sub translate second.offset) =
        presentation.toPlanarPresentation.stripDrawingEndpointInward orientation
          (.target secondEdge) translate := by
    simpa [secondEdge, ContractedEdge.sourceTag] using secondValue
  have thirdValue' :
      presentation.toPlanarPresentation.reverseStripGraphOrientation orientation
          ⟨third.tripleIndex, color⟩ (Cell.sub translate third.offset) =
        presentation.toPlanarPresentation.stripDrawingEndpointInward orientation
          (.target thirdEdge) translate := by
    simpa [thirdEdge, ContractedEdge.sourceTag] using thirdValue
  rw [firstValue', secondValue', thirdValue']
  simpa [firstEdge, secondEdge, thirdEdge] using endpointExactlyOne

/-- Every colored element satisfies its extracted post-contraction
constraint. -/
theorem ContinuousPlanarPresentation.reverseStripGraphOrientation_suppressedCoversElements
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (horizontal : problem.IsOneDimensional)
    (sourceInside :
      presentation.toPlanarPresentation.drawing
        |>.RoutePointsInExpandedVerticalBand)
    (collisionFree :
      presentation.toPlanarPresentation.FinalStripAssignmentsCollisionFree)
    (orientation :
      presentation.toPlanarPresentation.stripNormalizedOrthogonalDrawing
        |>.Orientation)
    (valid :
      presentation.toPlanarPresentation.stripNormalizedOrthogonalDrawing
        |>.IsOrientation orientation) :
    problem.SuppressedCoversElements
      (presentation.toPlanarPresentation.reverseStripGraphOrientation
        orientation) := by
  intro color atom atomLt translate
  by_cases degreeTwo : problem.degree color atom = 2
  · exact presentation.reverseStripGraphOrientation_element_degreeTwo
      wellFormed degree horizontal sourceInside collisionFree orientation valid
        color atom atomLt degreeTwo translate
  · have degreeCases :
        problem.degree color atom = 2 ∨ problem.degree color atom = 3 := by
      simpa using degree color atom atomLt
    have degreeThree : problem.degree color atom = 3 :=
      degreeCases.resolve_left degreeTwo
    exact presentation.reverseStripGraphOrientation_element_degreeThree
      wellFormed degree horizontal sourceInside collisionFree orientation valid
        color atom atomLt degreeThree translate

/-- An arbitrary valid orientation of the compiled strip drawing extracts a
valid suppressed 3DM orientation. -/
theorem ContinuousPlanarPresentation.reverseStripGraphOrientation_isSuppressedOrientation
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (horizontal : problem.IsOneDimensional)
    (sourceInside :
      presentation.toPlanarPresentation.drawing
        |>.RoutePointsInExpandedVerticalBand)
    (collisionFree :
      presentation.toPlanarPresentation.FinalStripAssignmentsCollisionFree)
    (orientation :
      presentation.toPlanarPresentation.stripNormalizedOrthogonalDrawing
        |>.Orientation)
    (valid :
      presentation.toPlanarPresentation.stripNormalizedOrthogonalDrawing
        |>.IsOrientation orientation) :
    problem.IsSuppressedOrientation
      (presentation.toPlanarPresentation.reverseStripGraphOrientation
        orientation) :=
  ⟨presentation.reverseStripGraphOrientation_tripleCoherent
      wellFormed degree horizontal sourceInside collisionFree orientation valid,
    presentation.reverseStripGraphOrientation_suppressedCoversElements
      wellFormed degree horizontal sourceInside collisionFree orientation valid⟩

end PeriodicThreeDM

end LeanTrominoes
