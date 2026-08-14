/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationStripReverseEndpointOrientation

/-!
# Triple coherence of graph values read from a strip orientation
-/

namespace LeanTrominoes

open Gadget

namespace PeriodicThreeDM

set_option maxRecDepth 2048

/-- The graph assignment read from a valid strip orientation is coherent at
every translated triple vertex. -/
theorem ContinuousPlanarPresentation.reverseStripGraphOrientation_tripleCoherent
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
    problem.GraphTripleCoherent
      (presentation.toPlanarPresentation.reverseStripGraphOrientation
        orientation) := by
  intro tripleIndex indexLt translate
  let planar := presentation.toPlanarPresentation
  let redTag : IncidenceTag := ⟨tripleIndex, .red⟩
  let greenTag : IncidenceTag := ⟨tripleIndex, .green⟩
  let blueTag : IncidenceTag := ⟨tripleIndex, .blue⟩
  let redEndpoint := problem.contractedTripleEndpointForTag redTag
  let greenEndpoint := problem.contractedTripleEndpointForTag greenTag
  let blueEndpoint := problem.contractedTripleEndpointForTag blueTag
  have redTagMember := problem.tripleIncidenceTag_mem_incidenceTags
    tripleIndex indexLt .red
  have greenTagMember := problem.tripleIncidenceTag_mem_incidenceTags
    tripleIndex indexLt .green
  have blueTagMember := problem.tripleIncidenceTag_mem_incidenceTags
    tripleIndex indexLt .blue
  have redTripleMember := problem.contractedTripleEndpointForTag_mem
    wellFormed degree redTagMember
  have greenTripleMember := problem.contractedTripleEndpointForTag_mem
    wellFormed degree greenTagMember
  have redMember := problem.contractedTripleEndpoint_mem_contractedEndpoints
    redTripleMember
  have greenMember := problem.contractedTripleEndpoint_mem_contractedEndpoints
    greenTripleMember
  have redVertex := problem.contractedTripleEndpointForTag_vertex
    wellFormed degree redTagMember
  have greenVertex := problem.contractedTripleEndpointForTag_vertex
    wellFormed degree greenTagMember
  have blueVertex := problem.contractedTripleEndpointForTag_vertex
    wellFormed degree blueTagMember
  have redGreen := presentation.stripDrawingEndpointInward_eq_at_triple
    wellFormed degree horizontal sourceInside collisionFree orientation valid
      redMember tripleIndex redVertex greenVertex translate
  have greenBlue := presentation.stripDrawingEndpointInward_eq_at_triple
    wellFormed degree horizontal sourceInside collisionFree orientation valid
      greenMember tripleIndex greenVertex blueVertex translate
  change
    (!(planar.stripDrawingEndpointInward orientation redEndpoint translate)) =
        (!(planar.stripDrawingEndpointInward orientation greenEndpoint
          translate)) ∧
      (!(planar.stripDrawingEndpointInward orientation greenEndpoint
          translate)) =
        (!(planar.stripDrawingEndpointInward orientation blueEndpoint translate))
  exact ⟨congrArg (fun value : Bool => !value) redGreen,
    congrArg (fun value : Bool => !value) greenBlue⟩

end PeriodicThreeDM

end LeanTrominoes
