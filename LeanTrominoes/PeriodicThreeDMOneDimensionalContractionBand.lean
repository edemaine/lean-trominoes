/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicGridDrawingVerticalBandPolyline
import LeanTrominoes.PeriodicThreeDMContractionGeometry
import LeanTrominoes.PeriodicThreeDMOneDimensionalContraction

/-!
# Vertical-band preservation under one-dimensional 3DM contraction

Degree-two contraction joins one incidence route to a translated reverse of
another.  For a one-dimensional 3DM instance that translation is horizontal,
so contraction preserves the original drawing's open vertical halo.
-/

namespace LeanTrominoes

open Gadget
open PeriodicOrthocrossing

namespace PeriodicThreeDM

/-- Every genuine incidence route inherits a pointwise vertical-band bound
from the original drawing. -/
theorem PlanarPresentation.incidenceRoute_inExpandedVerticalBand
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (sourceInside :
      presentation.drawing.RoutePointsInExpandedVerticalBand)
    (color : WireColor) (atom : Nat) {incidence : Incidence}
    (member : incidence ∈ problem.incidences color atom) :
    presentation.drawing.PolylineInExpandedVerticalBand
      (presentation.incidenceRoute
        ⟨incidence.tripleIndex, color⟩) := by
  have tagMember :=
    incidenceTag_mem_of_incidence_mem
      problem color atom member
  have routeMember := presentation.incidenceRoute_mem tagMember
  intro point pointMember
  exact sourceInside _ routeMember point pointMember

/-- Every contracted edge route remains in the source drawing's open vertical
halo. -/
theorem PlanarPresentation.contractedEdgeRoute_inExpandedVerticalBand
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (horizontal : problem.IsOneDimensional)
    (sourceInside :
      presentation.drawing.RoutePointsInExpandedVerticalBand)
    {edge : ContractedEdge}
    (member : edge ∈ problem.contractedEdges) :
    presentation.drawing.PolylineInExpandedVerticalBand
      (presentation.contractedEdgeRoute edge) := by
  have edgeHorizontal :=
    contractedEdge_offset_vertical_eq_zero horizontal member
  simp only [contractedEdges, List.mem_flatMap] at member
  rcases member with ⟨color, _colorMember, member⟩
  simp only [contractedEdgesForColor, List.mem_flatMap] at member
  rcases member with ⟨atom, _atomMember, member⟩
  have metadata :=
    contractedEdgesForElement_metadata problem color atom member
  have incidenceMembers :=
    contractedEdgesForElement_incidence_members
      problem color atom member
  cases edge with
  | retained edgeColor edgeAtom incidence =>
      simp only [ContractedEdge.color,
        ContractedEdge.atom] at metadata
      have incidenceMember :
          incidence ∈ problem.incidences edgeColor edgeAtom := by
        simpa only [metadata.1, metadata.2,
          ContractedEdge.sourceIncidence] using incidenceMembers.1
      simpa [PlanarPresentation.contractedEdgeRoute] using
        presentation.incidenceRoute_inExpandedVerticalBand
          sourceInside edgeColor edgeAtom incidenceMember
  | through edgeColor edgeAtom first second =>
      simp only [ContractedEdge.color,
        ContractedEdge.atom] at metadata
      have firstMember :
          first ∈ problem.incidences edgeColor edgeAtom := by
        simpa only [metadata.1, metadata.2,
          ContractedEdge.sourceIncidence] using incidenceMembers.1
      have secondMember :
          second ∈ problem.incidences edgeColor edgeAtom := by
        simpa only [metadata.1, metadata.2,
          ContractedEdge.targetIncidence] using incidenceMembers.2.1
      have firstInside :=
        presentation.incidenceRoute_inExpandedVerticalBand
          sourceInside edgeColor edgeAtom firstMember
      have secondInside :=
        presentation.incidenceRoute_inExpandedVerticalBand
          sourceInside edgeColor edgeAtom secondMember
      have shiftHorizontal :
          (Cell.sub first.offset second.offset).2 = 0 := by
        simpa [ContractedEdge.toPeriodicEdge] using edgeHorizontal
      have translatedInside :=
        secondInside.translatePeriod shiftHorizontal
      have reversedInside := translatedInside.reverse
      exact firstInside.joinPolylines reversedInside

/-- If the original routes lie in the open vertical halo, so do all routes
stored by its one-dimensional contracted drawing. -/
theorem PlanarPresentation.contractedDrawing_routePointsInExpandedVerticalBand
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (horizontal : problem.IsOneDimensional)
    (sourceInside :
      presentation.drawing.RoutePointsInExpandedVerticalBand) :
    presentation.contractedDrawing.RoutePointsInExpandedVerticalBand := by
  intro route routeMember point pointMember
  simp only [PlanarPresentation.contractedDrawing,
    List.mem_map] at routeMember
  rcases routeMember with ⟨tagged, taggedMember, rfl⟩
  have inside :=
    presentation.contractedEdgeRoute_inExpandedVerticalBand
      horizontal sourceInside
      (List.fst_mem_of_mem_zipIdx taggedMember)
      point pointMember
  simpa [PeriodicGridDrawing.PositionInExpandedVerticalBand,
    PeriodicGridDrawing.gridSize,
    PlanarPresentation.contractedDrawing] using inside

end PeriodicThreeDM
end LeanTrominoes
