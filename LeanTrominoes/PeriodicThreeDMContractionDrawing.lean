import LeanTrominoes.PeriodicPlanarThreeDM
import LeanTrominoes.PeriodicThreeDMContraction
import LeanTrominoes.PeriodicOrthocrossingConstruction

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

/-- Incidence tags can equivalently be enumerated by triple index rather
than by the value/index pairs of `zipIdx`. -/
theorem incidenceTags_eq_range_flatMap (problem : PeriodicThreeDM) :
    problem.incidenceTags =
      (List.range problem.triples.length).flatMap tripleIncidenceTags := by
  unfold incidenceTags
  rw [← List.flatMap_map]
  congr 1
  rw [List.zipIdx_map_snd, List.range_eq_range']

/-- The three colored tags of one triple index are duplicate-free. -/
theorem tripleIncidenceTags_nodup (tripleIndex : Nat) :
    (tripleIncidenceTags tripleIndex).Nodup := by
  apply incidenceColors_nodup.map
  intro first second equality
  cases equality
  rfl

/-- Distinct triple indices contribute disjoint incidence-tag blocks. -/
theorem tripleIncidenceTags_disjoint
    {firstIndex secondIndex : Nat}
    (different : firstIndex ≠ secondIndex) :
    List.Disjoint
      (tripleIncidenceTags firstIndex)
      (tripleIncidenceTags secondIndex) := by
  rw [List.disjoint_left]
  intro tag firstMem secondMem
  simp only [tripleIncidenceTags, List.mem_map] at firstMem secondMem
  rcases firstMem with ⟨firstColor, _, rfl⟩
  rcases secondMem with ⟨secondColor, _, equality⟩
  cases equality
  exact different rfl

/-- Every original incidence edge has one unique tag-list position. -/
theorem incidenceTags_nodup (problem : PeriodicThreeDM) :
    problem.incidenceTags.Nodup := by
  rw [incidenceTags_eq_range_flatMap, List.nodup_flatMap]
  exact
    ⟨fun index _ => tripleIncidenceTags_nodup index,
      List.nodup_range.imp fun different =>
        tripleIncidenceTags_disjoint different⟩

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
  problem.contractedGraph.vertices.map fun vertex =>
    presentation.drawing.vertexPosition
      problem.incidenceGraph vertex

/-- The planar drawing obtained by retaining or concatenating original
routes.  Its period is unchanged. -/
def PlanarPresentation.contractedDrawing
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) :
    PeriodicGridDrawing where
  gridSizePred := presentation.drawing.gridSizePred
  vertexPositions := presentation.contractedVertexPositions
  edgeRoutes :=
    problem.contractedEdges.map
      presentation.contractedEdgeRoute

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

end PeriodicThreeDM

end LeanTrominoes
