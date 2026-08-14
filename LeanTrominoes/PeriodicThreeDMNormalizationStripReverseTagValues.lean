/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationReverseElementOrientation
import LeanTrominoes.PeriodicThreeDMNormalizationStripReverseRouteCompatibility

/-!
# Incidence-tag values read from normalized strip orientations
-/

namespace LeanTrominoes

open Gadget

namespace PeriodicThreeDM

set_option maxRecDepth 2048

/-- At the source tag of an emitted edge, strip extraction is negation of the
inward value at that edge's source endpoint. -/
theorem PlanarPresentation.reverseStripGraphOrientation_sourceTag
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (orientation : presentation.stripNormalizedOrthogonalDrawing.Orientation)
    {edge : ContractedEdge}
    (edgeMember : edge ∈ problem.contractedEdges)
    (translate : Cell) :
    presentation.reverseStripGraphOrientation orientation edge.sourceTag
        translate =
      !(presentation.stripDrawingEndpointInward orientation (.source edge)
        translate) := by
  unfold PlanarPresentation.reverseStripGraphOrientation
  rw [problem.contractedTripleEndpointForTag_sourceTag
    wellFormed degree edgeMember]

/-- At the second tag of a through edge, strip extraction is negation of its
target triple endpoint's inward value. -/
theorem PlanarPresentation.reverseStripGraphOrientation_through_targetTag
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (orientation : presentation.stripNormalizedOrthogonalDrawing.Orientation)
    (color : WireColor) (atom : Nat) (first second : Incidence)
    (edgeMember :
      ContractedEdge.through color atom first second ∈
        problem.contractedEdges)
    (translate : Cell) :
    presentation.reverseStripGraphOrientation orientation
        (ContractedEdge.through color atom first second).targetTag translate =
      !(presentation.stripDrawingEndpointInward orientation
        (.target (ContractedEdge.through color atom first second)) translate) := by
  unfold PlanarPresentation.reverseStripGraphOrientation
  rw [problem.contractedTripleEndpointForTag_through_targetTag
    wellFormed degree color atom first second edgeMember]

/-- An extracted incidence carried by a retained edge equals the inward strip
value at its translated monochromatic target endpoint. -/
theorem ContinuousPlanarPresentation.reverseStripGraphOrientation_retained_eq_target
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
    (color : WireColor) (atom : Nat) (incidence : Incidence)
    (edgeMember :
      ContractedEdge.retained color atom incidence ∈ problem.contractedEdges)
    (sourceTranslate : Cell) :
    let planar := presentation.toPlanarPresentation
    let edge := ContractedEdge.retained color atom incidence
    let targetTranslate := Cell.add sourceTranslate incidence.offset
    planar.reverseStripGraphOrientation orientation edge.sourceTag
        sourceTranslate =
      planar.stripDrawingEndpointInward orientation (.target edge)
        targetTranslate := by
  dsimp only
  let planar := presentation.toPlanarPresentation
  let edge := ContractedEdge.retained color atom incidence
  let targetTranslate := Cell.add sourceTranslate incidence.offset
  have endpointDifferent := presentation.stripDrawingEndpointInward_ne
    wellFormed degree horizontal sourceInside collisionFree orientation valid
      edgeMember sourceTranslate
  have sourceValue := planar.reverseStripGraphOrientation_sourceTag
    wellFormed degree orientation edgeMember sourceTranslate
  have endpointDifferent' :
      planar.stripDrawingEndpointInward orientation (.source edge)
          sourceTranslate ≠
        planar.stripDrawingEndpointInward orientation (.target edge)
          targetTranslate := by
    simpa [planar, edge, targetTranslate, ContractedEdge.toPeriodicEdge] using
      endpointDifferent
  change planar.reverseStripGraphOrientation orientation edge.sourceTag
      sourceTranslate =
    planar.stripDrawingEndpointInward orientation (.target edge) targetTranslate
  calc
    _ = !(planar.stripDrawingEndpointInward orientation (.source edge)
          sourceTranslate) := sourceValue
    _ = planar.stripDrawingEndpointInward orientation (.target edge)
          targetTranslate :=
      (bool_eq_not_of_ne _ _ (Ne.symm endpointDifferent')).symm

/-- The two extracted incidences represented by a through edge are unequal. -/
theorem ContinuousPlanarPresentation.reverseStripGraphOrientation_through_ne
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
    (color : WireColor) (atom : Nat) (first second : Incidence)
    (edgeMember :
      ContractedEdge.through color atom first second ∈ problem.contractedEdges)
    (sourceTranslate : Cell) :
    let planar := presentation.toPlanarPresentation
    let edge := ContractedEdge.through color atom first second
    let targetTranslate := Cell.add sourceTranslate
      (Cell.sub first.offset second.offset)
    planar.reverseStripGraphOrientation orientation edge.sourceTag
        sourceTranslate ≠
      planar.reverseStripGraphOrientation orientation edge.targetTag
        targetTranslate := by
  dsimp only
  let planar := presentation.toPlanarPresentation
  let edge := ContractedEdge.through color atom first second
  let targetTranslate := Cell.add sourceTranslate
    (Cell.sub first.offset second.offset)
  have endpointDifferent := presentation.stripDrawingEndpointInward_ne
    wellFormed degree horizontal sourceInside collisionFree orientation valid
      edgeMember sourceTranslate
  have sourceValue := planar.reverseStripGraphOrientation_sourceTag
    wellFormed degree orientation edgeMember sourceTranslate
  have targetValue := planar.reverseStripGraphOrientation_through_targetTag
    wellFormed degree orientation color atom first second edgeMember
      targetTranslate
  have endpointDifferent' :
      planar.stripDrawingEndpointInward orientation (.source edge)
          sourceTranslate ≠
        planar.stripDrawingEndpointInward orientation (.target edge)
          targetTranslate := by
    simpa [planar, edge, targetTranslate, ContractedEdge.toPeriodicEdge] using
      endpointDifferent
  change planar.reverseStripGraphOrientation orientation edge.sourceTag
      sourceTranslate ≠
    planar.reverseStripGraphOrientation orientation edge.targetTag
      targetTranslate
  intro extractedEqual
  have complementsEqual :
      (!(planar.stripDrawingEndpointInward orientation (.source edge)
          sourceTranslate)) =
        (!(planar.stripDrawingEndpointInward orientation (.target edge)
          targetTranslate)) :=
    sourceValue.symm.trans (extractedEqual.trans targetValue)
  apply endpointDifferent'
  cases sourceInward :
      planar.stripDrawingEndpointInward orientation (.source edge)
        sourceTranslate <;>
    cases targetInward :
      planar.stripDrawingEndpointInward orientation (.target edge)
        targetTranslate <;>
    simp_all

end PeriodicThreeDM

end LeanTrominoes
