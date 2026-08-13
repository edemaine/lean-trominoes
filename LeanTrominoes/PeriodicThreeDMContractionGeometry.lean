/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMContractionDrawing
import LeanTrominoes.OrthogonalPolylineSymmetries

/-!
# Geometric invariants of periodic 3DM contraction

Concatenating the two routes at a suppressed degree-two element introduces
no new geometric segment.  The second route is merely translated and
traversed backward.  This file first packages orthogonality route-by-route
and then proves that the compatible contracted drawing remains orthogonal.
-/

namespace LeanTrominoes

open Gadget
open PeriodicOrthocrossing

namespace PeriodicThreeDM

/-- Every genuine incidence route occurs in the original drawing's route
list at the tag's stable index. -/
theorem PlanarPresentation.incidenceRoute_mem
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    {tag : IncidenceTag}
    (member : tag ∈ problem.incidenceTags) :
    presentation.incidenceRoute tag ∈
      presentation.drawing.edgeRoutes := by
  have tagIndexLt :
      problem.incidenceRouteIndex tag <
        problem.incidenceTags.length :=
    List.idxOf_lt_length_iff.mpr member
  have routeIndexLt :
      problem.incidenceRouteIndex tag <
        presentation.drawing.edgeRoutes.length := by
    rw [presentation.compatible.2.2.1,
      incidenceGraph_edges_length]
    exact tagIndexLt
  unfold PlanarPresentation.incidenceRoute
    PeriodicGridDrawing.edgeRoute
  rw [List.getD_eq_getElem _ _ routeIndexLt]
  exact List.getElem_mem routeIndexLt

/-- Every genuine incidence route is an orthogonal polyline. -/
theorem PlanarPresentation.incidenceRoute_orthogonal
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    {tag : IncidenceTag}
    (member : tag ∈ problem.incidenceTags) :
    OrthogonalPolyline
      (presentation.incidenceRoute tag) := by
  exact
    (PeriodicGridDrawing.isOrthogonal_iff_routes
      presentation.drawing).1 presentation.orthogonal
      (presentation.incidenceRoute tag)
      (presentation.incidenceRoute_mem member)

/-- Every contracted edge route is orthogonal. -/
theorem PlanarPresentation.contractedEdgeRoute_orthogonal
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (color : WireColor) (atom : Nat)
    {edge : ContractedEdge}
    (member :
      edge ∈ problem.contractedEdgesForElement color atom) :
    OrthogonalPolyline
      (presentation.contractedEdgeRoute edge) := by
  have metadata :=
    contractedEdgesForElement_metadata
      problem color atom member
  have incidenceMembers :=
    contractedEdgesForElement_incidence_members
      problem color atom member
  cases edge with
  | retained edgeColor edgeAtom incidence =>
      simp only [ContractedEdge.color,
        ContractedEdge.atom] at metadata
      rcases metadata with ⟨rfl, rfl⟩
      have incidenceMember :
          incidence ∈ problem.incidences edgeColor edgeAtom := by
        simpa [ContractedEdge.sourceIncidence] using
          incidenceMembers.1
      exact
        presentation.incidenceRoute_orthogonal
          (incidenceTag_mem_of_incidence_mem
            problem edgeColor edgeAtom incidenceMember)
  | through edgeColor edgeAtom first second =>
      simp only [ContractedEdge.color,
        ContractedEdge.atom] at metadata
      rcases metadata with ⟨rfl, rfl⟩
      have firstMember :
          first ∈ problem.incidences edgeColor edgeAtom := by
        simpa [ContractedEdge.sourceIncidence] using
          incidenceMembers.1
      have secondMember :
          second ∈ problem.incidences edgeColor edgeAtom := by
        simpa [ContractedEdge.targetIncidence] using
          incidenceMembers.2.1
      have firstOrthogonal :=
        presentation.incidenceRoute_orthogonal
          (incidenceTag_mem_of_incidence_mem
            problem edgeColor edgeAtom firstMember)
      have secondOrthogonal :=
        presentation.incidenceRoute_orthogonal
          (incidenceTag_mem_of_incidence_mem
            problem edgeColor edgeAtom secondMember)
      have firstEndpoints :=
        presentation.incidenceRoute_endpoints_of_incidence
          edgeColor edgeAtom firstMember
      have secondEndpoints :=
        presentation.incidenceRoute_endpoints_of_incidence
          edgeColor edgeAtom secondMember
      let translate :=
        presentation.drawing.periodTranslation
          (Cell.sub first.offset second.offset)
      let reversedSecond :=
        (translatePolyline translate
          (presentation.incidenceRoute
            ⟨second.tripleIndex, edgeColor⟩)).reverse
      have reversedOrthogonal :
          OrthogonalPolyline reversedSecond :=
        (secondOrthogonal.translate translate).reverse
      have boundary :
          (presentation.incidenceRoute
              ⟨first.tripleIndex, edgeColor⟩).getLast? =
            reversedSecond.head? := by
        rw [firstEndpoints.2]
        simp only [reversedSecond, List.head?_reverse,
          translatePolyline, List.getLast?_map,
          secondEndpoints.2, Option.map_some]
        simpa [translate] using
          congrArg some
            (periodTranslation_element_endpoint_sub
              presentation.drawing
              (presentation.drawing.vertexPosition
                problem.incidenceGraph
                (.element edgeColor edgeAtom))
              first.offset second.offset).symm
      unfold PlanarPresentation.contractedEdgeRoute
      apply isChain_joinPolylines
      · exact firstOrthogonal
      · simpa [reversedSecond, translate,
          PlanarPresentation.reversedIncidenceRouteAt,
          OrthogonalPolyline] using
          reversedOrthogonal
      · simpa [reversedSecond, translate,
          PlanarPresentation.reversedIncidenceRouteAt] using boundary

/-- Contracting degree-two elements preserves orthogonality of the complete
periodic drawing. -/
theorem PlanarPresentation.contractedDrawing_isOrthogonal
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) :
    presentation.contractedDrawing.IsOrthogonal := by
  apply
    (PeriodicGridDrawing.isOrthogonal_iff_routes
      presentation.contractedDrawing).2
  intro route routeMem
  simp only [PlanarPresentation.contractedDrawing,
    List.mem_map] at routeMem
  rcases routeMem with
    ⟨taggedEdge, taggedEdgeMem, rfl⟩
  have edgeMem :
      taggedEdge.1 ∈ problem.contractedEdges :=
    List.fst_mem_of_mem_zipIdx taggedEdgeMem
  simp only [contractedEdges,
    List.mem_flatMap] at edgeMem
  rcases edgeMem with ⟨color, colorMem, edgeMem⟩
  simp only [contractedEdgesForColor,
    List.mem_flatMap] at edgeMem
  rcases edgeMem with ⟨atom, atomMem, edgeMem⟩
  exact
    presentation.contractedEdgeRoute_orthogonal
      color atom edgeMem

end PeriodicThreeDM

end LeanTrominoes
