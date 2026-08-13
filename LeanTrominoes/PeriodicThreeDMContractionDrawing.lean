/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarThreeDM
import LeanTrominoes.PeriodicThreeDMContraction
import LeanTrominoes.PeriodicOrthocrossingCorrectness

/-!
# Drawing the contracted periodic 3DM graph

The contracted graph reuses a planar 3DM presentation geometrically.
Retained edges keep their original route.  For a degree-two colored element,
the route of the first incidence is joined to a reversed periodic translate
of the second route at their common element endpoint.

This file first establishes reliable lookup of original routes by
`IncidenceTag`, then defines the concatenated route list.  The incidence
metadata stored in `ContractedEdge` keeps the construction independent of
coordinate-based endpoint recognition.
-/

namespace LeanTrominoes

open Gadget
open PeriodicOrthocrossing

namespace PeriodicThreeDM

/-- The tag named by a genuine colored-element incidence occurs in the
global edge/tag list. -/
theorem incidenceTag_mem_of_incidence_mem
    (problem : PeriodicThreeDM) (color : WireColor) (atom : Nat)
    {incidence : Incidence}
    (member : incidence ∈ problem.incidences color atom) :
    (⟨incidence.tripleIndex, color⟩ : IncidenceTag) ∈
      problem.incidenceTags := by
  rw [incidenceTags_eq_range_flatMap]
  apply List.mem_flatMap.mpr
  refine
    ⟨incidence.tripleIndex,
      List.mem_range.mpr
        (incidence_tripleIndex_lt problem color atom member), ?_⟩
  cases color <;>
    simp [tripleIncidenceTags, incidenceColors]

/-- Membership in an incidence list recovers the actual triple reference
that generated the incidence record. -/
theorem reference_eq_of_incidence_mem
    (problem : PeriodicThreeDM) (color : WireColor) (atom : Nat)
    {incidence : Incidence}
    (member : incidence ∈ problem.incidences color atom) :
    let triple :=
      problem.triples.getD incidence.tripleIndex default
    (triple.reference color).atom = atom ∧
      (triple.reference color).offset = incidence.offset := by
  simp only [incidences, List.mem_filterMap] at member
  rcases member with ⟨tripleIndex, tripleIndexMem, produced⟩
  split at produced
  next same =>
    injection produced with incidenceEq
    subst incidence
    exact ⟨same, rfl⟩
  next different =>
    simp at produced

/-- Stable list index used to retrieve the route of an incidence tag. -/
def incidenceRouteIndex (problem : PeriodicThreeDM)
    (tag : IncidenceTag) : Nat :=
  problem.incidenceTags.idxOf tag

/-- Route of one original incidence edge in a planar presentation. -/
def PlanarPresentation.incidenceRoute
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (tag : IncidenceTag) : List Cell :=
  presentation.drawing.edgeRoute
    (problem.incidenceRouteIndex tag)

/-- A genuine tag and its first-index position occur together in the
tag-list `zipIdx`. -/
theorem incidenceTag_zipIdx_mem
    (problem : PeriodicThreeDM) {tag : IncidenceTag}
    (member : tag ∈ problem.incidenceTags) :
    (tag, problem.incidenceRouteIndex tag) ∈
      problem.incidenceTags.zipIdx := by
  rw [List.mem_zipIdx_iff_getElem?,
    List.getElem?_eq_some_iff]
  have indexLt :
      problem.incidenceRouteIndex tag <
        problem.incidenceTags.length := by
    exact List.idxOf_lt_length_iff.mpr member
  exact
    ⟨indexLt,
      List.idxOf_get indexLt⟩

/-- The incidence graph edge at a genuine tag's route index is exactly the
edge reconstructed from that tag. -/
theorem incidenceEdge_zipIdx_mem
    (problem : PeriodicThreeDM) {tag : IncidenceTag}
    (member : tag ∈ problem.incidenceTags) :
    (problem.incidenceEdgeAt tag,
        problem.incidenceRouteIndex tag) ∈
      problem.incidenceGraph.edges.zipIdx := by
  rw [incidenceGraph_edges_eq_tags_map,
    List.mem_zipIdx_iff_getElem?,
    List.getElem?_eq_some_iff]
  have indexLt :
      problem.incidenceRouteIndex tag <
        problem.incidenceTags.length := by
    exact List.idxOf_lt_length_iff.mpr member
  refine ⟨by simpa using indexLt, ?_⟩
  simp only [List.getElem_map]
  congr 1
  exact List.idxOf_get indexLt

/-- Route matching at a genuine tag, with endpoints stated using the
tag-derived incidence edge. -/
theorem PlanarPresentation.incidenceRoute_endpoints
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    {tag : IncidenceTag} (member : tag ∈ problem.incidenceTags) :
    (presentation.incidenceRoute tag).head? =
        some (presentation.drawing.vertexPosition
          problem.incidenceGraph
          (problem.incidenceEdgeAt tag).source) ∧
      (presentation.incidenceRoute tag).getLast? =
        some (Cell.add
          (presentation.drawing.vertexPosition
            problem.incidenceGraph
            (problem.incidenceEdgeAt tag).target)
          (presentation.drawing.periodTranslation
            (problem.incidenceEdgeAt tag).offset)) := by
  exact presentation.compatible.2.2.2.2.2
    (problem.incidenceEdgeAt tag,
      problem.incidenceRouteIndex tag)
    (incidenceEdge_zipIdx_mem problem member)

/-- Route endpoints specialized to an incidence of a named colored element. -/
theorem PlanarPresentation.incidenceRoute_endpoints_of_incidence
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (color : WireColor) (atom : Nat) {incidence : Incidence}
    (member : incidence ∈ problem.incidences color atom) :
    let tag : IncidenceTag := ⟨incidence.tripleIndex, color⟩
    (presentation.incidenceRoute tag).head? =
        some (presentation.drawing.vertexPosition
          problem.incidenceGraph
          (.triple incidence.tripleIndex)) ∧
      (presentation.incidenceRoute tag).getLast? =
        some (Cell.add
          (presentation.drawing.vertexPosition
            problem.incidenceGraph (.element color atom))
          (presentation.drawing.periodTranslation
            incidence.offset)) := by
  let tag : IncidenceTag := ⟨incidence.tripleIndex, color⟩
  have tagMember :=
    incidenceTag_mem_of_incidence_mem
      problem color atom member
  have endpoints :=
    presentation.incidenceRoute_endpoints tagMember
  have reference :=
    reference_eq_of_incidence_mem
      problem color atom member
  have indexLt :=
    incidence_tripleIndex_lt problem color atom member
  rw [incidenceEdgeAt_eq_of_tag_mem problem tagMember] at endpoints
  simp only [incidenceEdge] at endpoints
  have tripleGetD :
      problem.triples.getD incidence.tripleIndex default =
        problem.triples[incidence.tripleIndex]'indexLt := by
    exact List.getD_eq_getElem _ _ indexLt
  rw [← tripleGetD] at endpoints
  rw [reference.1, reference.2] at endpoints
  exact endpoints

/-- `joinPolylines` preserves the last point of its second argument whenever
the two nonempty polylines meet at their boundary.  This version also covers
a singleton second polyline. -/
theorem joinPolylines_getLast?_of_boundary
    {first second : List Cell} {boundary last : Cell}
    (firstLast : first.getLast? = some boundary)
    (secondHead : second.head? = some boundary)
    (secondLast : second.getLast? = some last) :
    (joinPolylines first second).getLast? = some last := by
  cases second with
  | nil =>
      simp at secondHead
  | cons head tail =>
      cases tail with
      | nil =>
          simp only [List.head?_cons, Option.some.injEq] at secondHead
          simp only [List.getLast?_singleton, Option.some.injEq] at secondLast
          subst boundary
          subst last
          simpa [joinPolylines] using firstLast
      | cons next rest =>
          exact
            (joinPolylines_getLast?_of_second
              (first := first)
              (second := head :: next :: rest) (by simp)).trans
              secondLast

/-- Translate and reverse the second incidence route so that its colored
element endpoint is expressed at the translate reached by the first
incidence. -/
def PlanarPresentation.reversedIncidenceRouteAt
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (color : WireColor) (first second : Incidence) :
    List Cell :=
  (translatePolyline
    (presentation.drawing.periodTranslation
      (Cell.sub first.offset second.offset))
    (presentation.incidenceRoute
      ⟨second.tripleIndex, color⟩)).reverse

/-- Route of one retained or through edge in the contracted graph. -/
def PlanarPresentation.contractedEdgeRoute
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) :
    ContractedEdge → List Cell
  | .retained color _atom incidence =>
      presentation.incidenceRoute
        ⟨incidence.tripleIndex, color⟩
  | .through color _atom first second =>
      joinPolylines
        (presentation.incidenceRoute
          ⟨first.tripleIndex, color⟩)
        (presentation.reversedIncidenceRouteAt
          color first second)

/-- Original positions restricted to the vertices retained by contraction. -/
def PlanarPresentation.contractedVertexPositions
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) : List Cell :=
  problem.contractedGraph.vertices.zipIdx.map fun tagged =>
    presentation.drawing.vertexPosition
      problem.incidenceGraph tagged.1

/-- The planar drawing obtained by retaining or concatenating original
routes.  Its period is unchanged. -/
def PlanarPresentation.contractedDrawing
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) :
    PeriodicGridDrawing where
  gridSizePred := presentation.drawing.gridSizePred
  vertexPositions := presentation.contractedVertexPositions
  edgeRoutes :=
    problem.contractedEdges.zipIdx.map fun tagged =>
      presentation.contractedEdgeRoute tagged.1

/-- Translation by the incidence-offset difference carries the second
element endpoint to the first element endpoint. -/
theorem periodTranslation_element_endpoint_sub
    (drawing : PeriodicGridDrawing)
    (elementPosition : Cell) (firstOffset secondOffset : Cell) :
    Cell.add
        (drawing.periodTranslation
          (Cell.sub firstOffset secondOffset))
        (Cell.add elementPosition
          (drawing.periodTranslation secondOffset)) =
      Cell.add elementPosition
        (drawing.periodTranslation firstOffset) := by
  simp [PeriodicGridDrawing.periodTranslation,
    Cell.scale, Cell.sub, Cell.add]
  constructor <;> ring

/-- Translation by the incidence-offset difference places the second
triple endpoint at the target translate of a through edge. -/
theorem periodTranslation_triple_endpoint_sub
    (drawing : PeriodicGridDrawing)
    (triplePosition : Cell) (firstOffset secondOffset : Cell) :
    Cell.add
        (drawing.periodTranslation
          (Cell.sub firstOffset secondOffset))
        triplePosition =
      Cell.add triplePosition
        (drawing.periodTranslation
          (Cell.sub firstOffset secondOffset)) := by
  simp [PeriodicGridDrawing.periodTranslation,
    Cell.scale, Cell.sub, Cell.add, add_comm]

/-- Endpoint theorem for every edge generated by one colored element,
stated in the original drawing's vertex coordinates. -/
theorem PlanarPresentation.contractedEdgeRoute_endpoints
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (color : WireColor) (atom : Nat)
    {edge : ContractedEdge}
    (member :
      edge ∈ problem.contractedEdgesForElement color atom) :
    (presentation.contractedEdgeRoute edge).head? =
        some (presentation.drawing.vertexPosition
          problem.incidenceGraph edge.toPeriodicEdge.source) ∧
      (presentation.contractedEdgeRoute edge).getLast? =
        some (Cell.add
          (presentation.drawing.vertexPosition
            problem.incidenceGraph edge.toPeriodicEdge.target)
          (presentation.drawing.periodTranslation
            edge.toPeriodicEdge.offset)) := by
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
      simpa [PlanarPresentation.contractedEdgeRoute,
        ContractedEdge.toPeriodicEdge] using
          presentation.incidenceRoute_endpoints_of_incidence
            edgeColor edgeAtom incidenceMember
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
      have firstEndpoints :
          (presentation.incidenceRoute
              ⟨first.tripleIndex, edgeColor⟩).head? =
              some (presentation.drawing.vertexPosition
                problem.incidenceGraph
                (.triple first.tripleIndex)) ∧
            (presentation.incidenceRoute
              ⟨first.tripleIndex, edgeColor⟩).getLast? =
              some (Cell.add
                (presentation.drawing.vertexPosition
                  problem.incidenceGraph
                  (.element edgeColor edgeAtom))
                (presentation.drawing.periodTranslation
                  first.offset)) := by
        simpa using
        presentation.incidenceRoute_endpoints_of_incidence
          edgeColor edgeAtom firstMember
      have secondEndpoints :
          (presentation.incidenceRoute
              ⟨second.tripleIndex, edgeColor⟩).head? =
              some (presentation.drawing.vertexPosition
                problem.incidenceGraph
                (.triple second.tripleIndex)) ∧
            (presentation.incidenceRoute
              ⟨second.tripleIndex, edgeColor⟩).getLast? =
              some (Cell.add
                (presentation.drawing.vertexPosition
                  problem.incidenceGraph
                  (.element edgeColor edgeAtom))
                (presentation.drawing.periodTranslation
                  second.offset)) := by
        simpa using
        presentation.incidenceRoute_endpoints_of_incidence
          edgeColor edgeAtom secondMember
      let firstRoute :=
        presentation.incidenceRoute
          ⟨first.tripleIndex, edgeColor⟩
      let secondRoute :=
        presentation.incidenceRoute
          ⟨second.tripleIndex, edgeColor⟩
      let translate :=
        presentation.drawing.periodTranslation
          (Cell.sub first.offset second.offset)
      let reversedSecond :=
        (translatePolyline translate secondRoute).reverse
      change
        firstRoute.head? =
            some (presentation.drawing.vertexPosition
              problem.incidenceGraph
              (.triple first.tripleIndex)) ∧
          firstRoute.getLast? =
            some (Cell.add
              (presentation.drawing.vertexPosition
                problem.incidenceGraph
                (.element edgeColor edgeAtom))
              (presentation.drawing.periodTranslation
                first.offset)) at firstEndpoints
      change
        secondRoute.head? =
            some (presentation.drawing.vertexPosition
              problem.incidenceGraph
              (.triple second.tripleIndex)) ∧
          secondRoute.getLast? =
            some (Cell.add
              (presentation.drawing.vertexPosition
                problem.incidenceGraph
                (.element edgeColor edgeAtom))
              (presentation.drawing.periodTranslation
                second.offset)) at secondEndpoints
      have firstNonempty : firstRoute ≠ [] := by
        intro empty
        rw [empty] at firstEndpoints
        simp at firstEndpoints
      have reversedHead :
          reversedSecond.head? =
            some (Cell.add
              (presentation.drawing.vertexPosition
                problem.incidenceGraph
                (.element edgeColor edgeAtom))
              (presentation.drawing.periodTranslation
                first.offset)) := by
        simp only [reversedSecond, List.head?_reverse,
          translatePolyline, List.getLast?_map,
          secondRoute, secondEndpoints.2, Option.map_some]
        simpa [translate] using
          periodTranslation_element_endpoint_sub
          presentation.drawing
          (presentation.drawing.vertexPosition
            problem.incidenceGraph
            (.element edgeColor edgeAtom))
          first.offset second.offset
      have reversedLast :
          reversedSecond.getLast? =
            some (Cell.add
              (presentation.drawing.vertexPosition
                problem.incidenceGraph
                (.triple second.tripleIndex))
              (presentation.drawing.periodTranslation
                (Cell.sub first.offset second.offset))) := by
        simp only [reversedSecond, List.getLast?_reverse,
          translatePolyline, List.head?_map,
          secondRoute, secondEndpoints.1, Option.map_some]
        simpa [translate] using
          periodTranslation_triple_endpoint_sub
          presentation.drawing
          (presentation.drawing.vertexPosition
            problem.incidenceGraph
            (.triple second.tripleIndex))
          first.offset second.offset
      constructor
      · change
          (joinPolylines firstRoute reversedSecond).head? =
            some (presentation.drawing.vertexPosition
              problem.incidenceGraph
              (.triple first.tripleIndex))
        exact
          (joinPolylines_head?_of_first
            (first := firstRoute)
            (second := reversedSecond) firstNonempty).trans
              firstEndpoints.1
      · have joinedLast :=
          joinPolylines_getLast?_of_boundary
            firstEndpoints.2 reversedHead reversedLast
        change
          (joinPolylines firstRoute reversedSecond).getLast? =
            some (Cell.add
              (presentation.drawing.vertexPosition
                problem.incidenceGraph
                (.triple second.tripleIndex))
              (presentation.drawing.periodTranslation
                (Cell.sub first.offset second.offset)))
        exact joinedLast

/-- Every retained contracted vertex was already a vertex of the original
3DM incidence graph. -/
theorem contractedGraph_vertex_mem_incidenceGraph
    (problem : PeriodicThreeDM) {vertex : PeriodicThreeDMVertex}
    (member : vertex ∈ problem.contractedGraph.vertices) :
    vertex ∈ problem.incidenceGraph.vertices := by
  simp only [contractedGraph, List.mem_append] at member
  rcases member with tripleMember | elementMember
  · exact List.mem_append_left _ tripleMember
  · apply List.mem_append_right
    simp only [contractedElementVertices,
      List.mem_flatMap] at elementMember
    rcases elementMember with
      ⟨color, colorMem, elementMember⟩
    simp only [contractedElementVerticesForColor,
      List.mem_map] at elementMember
    rcases elementMember with
      ⟨atom, atomMember, rfl⟩
    have atomLt : atom < problem.elementCount color := by
      simpa using (List.mem_filter.mp atomMember).1
    cases color with
    | red =>
        apply List.mem_append_left
        apply List.mem_append_left
        exact
          (coloredElementVertices_mem_iff
            problem .red atom).2 atomLt
    | green =>
        apply List.mem_append_left
        apply List.mem_append_right
        exact
          (coloredElementVertices_mem_iff
            problem .green atom).2 atomLt
    | blue =>
        apply List.mem_append_right
        exact
          (coloredElementVertices_mem_iff
            problem .blue atom).2 atomLt

/-- Looking up a listed original vertex position returns an actual entry in
the presentation's position list. -/
theorem PlanarPresentation.vertexPosition_mem
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    {vertex : PeriodicThreeDMVertex}
    (member : vertex ∈ problem.incidenceGraph.vertices) :
    presentation.drawing.vertexPosition
        problem.incidenceGraph vertex ∈
      presentation.drawing.vertexPositions := by
  have indexLt :
      problem.incidenceGraph.vertices.idxOf vertex <
        problem.incidenceGraph.vertices.length :=
    List.idxOf_lt_length_iff.mpr member
  have positionIndexLt :
      problem.incidenceGraph.vertices.idxOf vertex <
        presentation.drawing.vertexPositions.length := by
    rwa [presentation.compatible.2.1]
  unfold PeriodicGridDrawing.vertexPosition
  rw [List.getD_eq_getElem _ _ positionIndexLt]
  exact List.getElem_mem positionIndexLt

/-- Original position lookup is injective on listed incidence-graph
vertices because both presentation lists are duplicate-free and aligned. -/
theorem PlanarPresentation.vertexPosition_injective_on
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    {first second : PeriodicThreeDMVertex}
    (firstMember : first ∈ problem.incidenceGraph.vertices)
    (secondMember : second ∈ problem.incidenceGraph.vertices)
    (equal :
      presentation.drawing.vertexPosition
          problem.incidenceGraph first =
        presentation.drawing.vertexPosition
          problem.incidenceGraph second) :
    first = second := by
  have firstIndexLt :
      problem.incidenceGraph.vertices.idxOf first <
        problem.incidenceGraph.vertices.length :=
    List.idxOf_lt_length_iff.mpr firstMember
  have secondIndexLt :
      problem.incidenceGraph.vertices.idxOf second <
        problem.incidenceGraph.vertices.length :=
    List.idxOf_lt_length_iff.mpr secondMember
  have firstPositionLt :
      problem.incidenceGraph.vertices.idxOf first <
        presentation.drawing.vertexPositions.length := by
    rwa [presentation.compatible.2.1]
  have secondPositionLt :
      problem.incidenceGraph.vertices.idxOf second <
        presentation.drawing.vertexPositions.length := by
    rwa [presentation.compatible.2.1]
  unfold PeriodicGridDrawing.vertexPosition at equal
  rw [List.getD_eq_getElem _ _ firstPositionLt,
    List.getD_eq_getElem _ _ secondPositionLt] at equal
  have indicesEqual :
      problem.incidenceGraph.vertices.idxOf first =
        problem.incidenceGraph.vertices.idxOf second :=
    (presentation.compatible.2.2.2.1.getElem_inj_iff).mp equal
  calc
    first =
        problem.incidenceGraph.vertices[
          problem.incidenceGraph.vertices.idxOf first]'firstIndexLt :=
      (List.idxOf_get firstIndexLt).symm
    _ =
        problem.incidenceGraph.vertices[
          problem.incidenceGraph.vertices.idxOf second]'secondIndexLt := by
      simp only [indicesEqual]
    _ = second :=
      List.idxOf_get secondIndexLt

/-- The zip-index implementation of contracted positions is extensionally
the direct map over contracted vertices. -/
theorem PlanarPresentation.contractedVertexPositions_eq_map
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) :
    presentation.contractedVertexPositions =
      problem.contractedGraph.vertices.map fun vertex =>
        presentation.drawing.vertexPosition
          problem.incidenceGraph vertex := by
  unfold PlanarPresentation.contractedVertexPositions
  calc
    _ =
        (problem.contractedGraph.vertices.zipIdx.map Prod.fst).map
          (fun vertex =>
            presentation.drawing.vertexPosition
              problem.incidenceGraph vertex) := by
      rw [List.map_map]
      rfl
    _ = _ := by
      rw [List.zipIdx_map_fst]

/-- Contracted drawing lookup agrees with the original position of every
retained vertex. -/
theorem PlanarPresentation.contractedDrawing_vertexPosition
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    {vertex : PeriodicThreeDMVertex}
    (member : vertex ∈ problem.contractedGraph.vertices) :
    presentation.contractedDrawing.vertexPosition
        problem.contractedGraph vertex =
      presentation.drawing.vertexPosition
        problem.incidenceGraph vertex := by
  have indexLt :
      problem.contractedGraph.vertices.idxOf vertex <
        problem.contractedGraph.vertices.length :=
    List.idxOf_lt_length_iff.mpr member
  have taggedMember :
      (vertex, problem.contractedGraph.vertices.idxOf vertex) ∈
        problem.contractedGraph.vertices.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?,
      List.getElem?_eq_some_iff]
    exact ⟨indexLt, List.idxOf_get indexLt⟩
  unfold PeriodicGridDrawing.vertexPosition
    PlanarPresentation.contractedDrawing
    PlanarPresentation.contractedVertexPositions
  exact
    getD_map_zipIdx_of_mem
      problem.contractedGraph.vertices
      (fun tagged =>
        presentation.drawing.vertexPosition
          problem.incidenceGraph tagged.1)
      (0, 0) taggedMember

/-- Contracted vertex positions remain pairwise distinct. -/
theorem PlanarPresentation.contractedVertexPositions_nodup
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) :
    presentation.contractedVertexPositions.Nodup := by
  rw [presentation.contractedVertexPositions_eq_map]
  apply List.Nodup.map_on
  · intro first firstMem second secondMem equal
    exact presentation.vertexPosition_injective_on
      (contractedGraph_vertex_mem_incidenceGraph
        problem firstMem)
      (contractedGraph_vertex_mem_incidenceGraph
        problem secondMem) equal
  · exact contractedGraph_vertices_nodup problem

/-- Every retained vertex stays in the open fundamental square. -/
theorem PlanarPresentation.contractedPositions_in_fundamental_square
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) :
    ∀ position ∈ presentation.contractedVertexPositions,
      presentation.contractedDrawing.PositionInFundamentalSquare
        position := by
  intro position positionMem
  rw [presentation.contractedVertexPositions_eq_map] at positionMem
  rcases List.mem_map.mp positionMem with
    ⟨vertex, vertexMem, rfl⟩
  have originalVertexMem :=
    contractedGraph_vertex_mem_incidenceGraph
      problem vertexMem
  have originalPositionMem :=
    presentation.vertexPosition_mem originalVertexMem
  exact presentation.compatible.2.2.2.2.1 _
    originalPositionMem

/-- Indexed lookup in the contracted route list returns the route belonging
to the same contracted-edge occurrence. -/
theorem PlanarPresentation.contractedDrawing_edgeRoute
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    {tagged : ContractedEdge × Nat}
    (member : tagged ∈ problem.contractedEdges.zipIdx) :
    presentation.contractedDrawing.edgeRoute tagged.2 =
      presentation.contractedEdgeRoute tagged.1 := by
  unfold PeriodicGridDrawing.edgeRoute
    PlanarPresentation.contractedDrawing
  exact
    getD_map_zipIdx_of_mem problem.contractedEdges
      (fun tagged =>
        presentation.contractedEdgeRoute tagged.1)
      [] member

/-- Every indexed graph edge comes from the contracted-edge occurrence at
the same list index. -/
theorem contractedGraph_edge_zipIdx
    (problem : PeriodicThreeDM)
    {taggedGraphEdge :
      PeriodicEdge PeriodicThreeDMVertex × Nat}
    (member :
      taggedGraphEdge ∈ problem.contractedGraph.edges.zipIdx) :
    ∃ edge : ContractedEdge,
      (edge, taggedGraphEdge.2) ∈
        problem.contractedEdges.zipIdx ∧
      edge.toPeriodicEdge = taggedGraphEdge.1 := by
  have indexLt :
      taggedGraphEdge.2 < problem.contractedEdges.length := by
    simpa [contractedGraph] using
      List.snd_lt_of_mem_zipIdx member
  let edge :=
    problem.contractedEdges[taggedGraphEdge.2]'indexLt
  have edgeMember :
      (edge, taggedGraphEdge.2) ∈
        problem.contractedEdges.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?,
      List.getElem?_eq_some_iff]
    exact ⟨indexLt, rfl⟩
  refine ⟨edge, edgeMember, ?_⟩
  have graphEdgeAt :=
    (List.mem_zipIdx' member).2.symm
  simpa [contractedGraph, edge] using graphEdgeAt

/-- The contracted routes match the endpoints and periodic offsets of the
contracted graph. -/
theorem PlanarPresentation.contractedDrawing_routesMatch
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) :
    presentation.contractedDrawing.RoutesMatch
      problem.contractedGraph := by
  intro taggedGraphEdge graphEdgeMem
  rcases contractedGraph_edge_zipIdx
      problem graphEdgeMem with
    ⟨edge, edgeZipMem, edgeEq⟩
  rw [← edgeEq]
  have edgeMem : edge ∈ problem.contractedEdges :=
    List.fst_mem_of_mem_zipIdx edgeZipMem
  simp only [contractedEdges,
    List.mem_flatMap] at edgeMem
  rcases edgeMem with ⟨color, colorMem, edgeMem⟩
  simp only [contractedEdgesForColor,
    List.mem_flatMap] at edgeMem
  rcases edgeMem with ⟨atom, atomMem, edgeMem⟩
  have endpoints :=
    presentation.contractedEdgeRoute_endpoints
      color atom edgeMem
  have graphEdgeListMem :
      edge.toPeriodicEdge ∈ problem.contractedGraph.edges := by
    rw [edgeEq]
    exact List.fst_mem_of_mem_zipIdx graphEdgeMem
  have endpointMembers :=
    (contractedGraph_isWellFormed problem).2
      edge.toPeriodicEdge graphEdgeListMem
  rw [presentation.contractedDrawing_edgeRoute edgeZipMem]
  rw [presentation.contractedDrawing_vertexPosition
      endpointMembers.1,
    presentation.contractedDrawing_vertexPosition
      endpointMembers.2]
  exact endpoints

/-- Route concatenation gives a finite presentation compatible with the
contracted periodic graph. -/
theorem PlanarPresentation.contractedDrawing_isCompatible
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) :
    presentation.contractedDrawing.IsCompatible
      problem.contractedGraph := by
  refine
    ⟨contractedGraph_isWellFormed problem, ?_, ?_, ?_, ?_, ?_⟩
  · simp [PlanarPresentation.contractedDrawing,
      PlanarPresentation.contractedVertexPositions]
  · simp [PlanarPresentation.contractedDrawing,
      contractedGraph]
  · exact presentation.contractedVertexPositions_nodup
  · exact
      presentation.contractedPositions_in_fundamental_square
  · exact presentation.contractedDrawing_routesMatch

end PeriodicThreeDM

end LeanTrominoes
