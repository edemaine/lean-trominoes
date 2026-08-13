/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMContractionCoverage
import LeanTrominoes.PeriodicThreeDMContractionGeometry

/-!
# Planarity infrastructure for contracted periodic 3DM drawings

A through edge is the first original incidence route followed by a translated
reverse of the second.  To transfer planarity, we first make that geometric
provenance explicit at segment level: joining introduces no segment, while
translation and reversal merely translate or reverse the original segments.
-/

namespace LeanTrominoes

open Gadget
open PeriodicOrthocrossing

namespace GridSegment

/-- Reverse the direction in which a segment is traversed. -/
def reverse (segment : GridSegment) : GridSegment :=
  ⟨segment.finish, segment.start⟩

@[simp]
theorem reverse_reverse (segment : GridSegment) :
    segment.reverse.reverse = segment := by
  cases segment
  rfl

@[simp]
theorem reverse_translate (segment : GridSegment) (offset : Cell) :
    (segment.translate offset).reverse =
      segment.reverse.translate offset := by
  rfl

/-- Closed containment is independent of segment traversal direction. -/
@[simp]
theorem contains_reverse (segment : GridSegment) (point : Cell) :
    segment.reverse.Contains point ↔ segment.Contains point := by
  simp only [reverse, Contains, IsHorizontal, IsVertical, Between]
  aesop

/-- Relative-interior containment is independent of segment traversal
direction. -/
@[simp]
theorem interiorContains_reverse
    (segment : GridSegment) (point : Cell) :
    segment.reverse.InteriorContains point ↔
      segment.InteriorContains point := by
  simp only [reverse, InteriorContains, IsHorizontal, IsVertical,
    StrictlyBetween]
  aesop

end GridSegment

/-- Translating every point of a polyline translates every segment. -/
theorem gridPolylineSegments_translatePolyline
    (offset : Cell) (points : List Cell) :
    gridPolylineSegments (translatePolyline offset points) =
      (gridPolylineSegments points).map
        (GridSegment.translate offset) := by
  induction points using List.twoStepInduction with
  | nil | singleton =>
      simp [translatePolyline, gridPolylineSegments]
  | cons_cons first second rest _ tailInduction =>
      simp only [translatePolyline, List.map_cons,
        gridPolylineSegments]
      change
        GridSegment.mk (Cell.add offset first) (Cell.add offset second) ::
            gridPolylineSegments
              (translatePolyline offset (second :: rest)) =
          GridSegment.translate offset (GridSegment.mk first second) ::
            (gridPolylineSegments (second :: rest)).map
              (GridSegment.translate offset)
      rw [tailInduction second]
      rfl

/-- Appending one point appends exactly the segment from the old last point
to the new point. -/
theorem gridPolylineSegments_append_singleton
    (first : Cell) (rest : List Cell) (last : Cell) :
    gridPolylineSegments ((first :: rest) ++ [last]) =
      gridPolylineSegments (first :: rest) ++
        [⟨(first :: rest).getLastD first, last⟩] := by
  induction rest generalizing first with
  | nil =>
      simp [gridPolylineSegments]
  | cons second rest induction =>
      simp only [List.cons_append, gridPolylineSegments,
        List.cons_append]
      congr 1
      change
        gridPolylineSegments ((second :: rest) ++ [last]) =
          gridPolylineSegments (second :: rest) ++
            [⟨(first :: second :: rest).getLastD first, last⟩]
      rw [induction second]
      congr 2

/-- Nonempty-list form of `gridPolylineSegments_append_singleton`. -/
theorem gridPolylineSegments_append_singleton_of_ne_nil
    (points : List Cell) (default last : Cell)
    (nonempty : points ≠ []) :
    gridPolylineSegments (points ++ [last]) =
      gridPolylineSegments points ++
        [⟨points.getLastD default, last⟩] := by
  cases points with
  | nil => exact (nonempty rfl).elim
  | cons first rest =>
      rw [gridPolylineSegments_append_singleton first rest last]
      congr 2

/-- Reversing a polyline reverses both the order and traversal direction of
its segments. -/
theorem gridPolylineSegments_reverse (points : List Cell) :
    gridPolylineSegments points.reverse =
      (gridPolylineSegments points).reverse.map
        GridSegment.reverse := by
  induction points using List.twoStepInduction with
  | nil | singleton =>
      simp [gridPolylineSegments]
  | cons_cons first second rest _ tailInduction =>
      rw [List.reverse_cons,
        gridPolylineSegments_append_singleton_of_ne_nil
          (second :: rest).reverse second first (by simp)]
      rw [tailInduction second]
      simp [gridPolylineSegments, GridSegment.reverse,
        List.map_append]

/-- Joining two polylines at a certified common endpoint concatenates their
segment lists exactly; in particular it creates no extra segment. -/
theorem gridPolylineSegments_joinPolylines
    {first second : List Cell} {boundary : Cell}
    (firstLast : first.getLast? = some boundary)
    (secondHead : second.head? = some boundary) :
    gridPolylineSegments (joinPolylines first second) =
      gridPolylineSegments first ++
        gridPolylineSegments second := by
  induction first using List.twoStepInduction with
  | nil =>
      simp at firstLast
  | singleton first =>
      cases second with
      | nil => simp at secondHead
      | cons head tail =>
          simp only [List.getLast?_singleton, Option.some.injEq] at firstLast
          simp only [List.head?_cons, Option.some.injEq] at secondHead
          subst first
          subst head
          simp [joinPolylines, gridPolylineSegments]
  | cons_cons first next rest _ tailInduction =>
      have tailLast :
          (next :: rest).getLast? = some boundary := by
        simpa using firstLast
      have tailSegments :=
        tailInduction next tailLast
      simpa [joinPolylines, gridPolylineSegments,
        tailSegments, List.cons_append]

namespace PeriodicThreeDM

/-- One segment of a contracted route together with the unique original
incidence segment from which it came.  `latticeShift` records the periodic
translation applied to the second half of a through edge. -/
structure ContractedSegmentOrigin where
  original : IndexedGridSegment
  tag : IncidenceTag
  latticeShift : Cell
  reversed : Bool
  deriving DecidableEq, Repr

/-- Realize an original segment after the translation and optional reversal
recorded by its contraction provenance. -/
def ContractedSegmentOrigin.realize
    (drawing : PeriodicGridDrawing)
    (origin : ContractedSegmentOrigin) : GridSegment :=
  let translated :=
    origin.original.segment.translate
      (drawing.periodTranslation origin.latticeShift)
  if origin.reversed then translated.reverse else translated

/-- Segment origins contributed by one original incidence route. -/
def PlanarPresentation.incidenceSegmentOrigins
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (tag : IncidenceTag) (latticeShift : Cell)
    (reversed : Bool) :
    List ContractedSegmentOrigin :=
  let tagged :=
    (gridPolylineSegments
      (presentation.incidenceRoute tag)).zipIdx
  let ordered := if reversed then tagged.reverse else tagged
  ordered.map fun item =>
    ⟨⟨problem.incidenceRouteIndex tag, item.2, item.1⟩,
      tag, latticeShift, reversed⟩

/-- Segment origins of a retained or through edge, in the order in which
the contracted route traverses them. -/
def PlanarPresentation.contractedSegmentOrigins
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) :
    ContractedEdge → List ContractedSegmentOrigin
  | edge@(.retained ..) =>
      presentation.incidenceSegmentOrigins
        edge.sourceTag (0, 0) false
  | edge@(.through _ _ first second) =>
      presentation.incidenceSegmentOrigins
          edge.sourceTag (0, 0) false ++
        presentation.incidenceSegmentOrigins
          edge.targetTag
          (Cell.sub first.offset second.offset) true

/-- Mapping a function over the values of an indexed list forgets exactly
the indices. -/
theorem map_zipIdx_value
    {α β : Type*} (values : List α) (function : α → β) :
    values.zipIdx.map (fun item => function item.1) =
      values.map function := by
  conv_rhs =>
    rw [← List.zipIdx_map_fst 0 values,
      List.map_map, Function.comp_def]

/-- Realizing a forward incidence-origin block simply translates every
original segment. -/
theorem PlanarPresentation.incidenceSegmentOrigins_realize_false
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (tag : IncidenceTag) (latticeShift : Cell) :
    (presentation.incidenceSegmentOrigins
        tag latticeShift false).map
          (ContractedSegmentOrigin.realize
            presentation.drawing) =
      (gridPolylineSegments
        (presentation.incidenceRoute tag)).map fun segment =>
          segment.translate
            (presentation.drawing.periodTranslation latticeShift) := by
  simp only [PlanarPresentation.incidenceSegmentOrigins,
    Bool.false_eq_true, ↓reduceIte, List.map_map]
  change
    (gridPolylineSegments
      (presentation.incidenceRoute tag)).zipIdx.map
        (fun item => item.1.translate
          (presentation.drawing.periodTranslation latticeShift)) =
      _
  exact map_zipIdx_value _ _

/-- Realizing a reversed incidence-origin block reverses the order and
traversal direction after translating every original segment. -/
theorem PlanarPresentation.incidenceSegmentOrigins_realize_true
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (tag : IncidenceTag) (latticeShift : Cell) :
    (presentation.incidenceSegmentOrigins
        tag latticeShift true).map
          (ContractedSegmentOrigin.realize
            presentation.drawing) =
      ((gridPolylineSegments
        (presentation.incidenceRoute tag)).map fun segment =>
          (segment.translate
            (presentation.drawing.periodTranslation
              latticeShift)).reverse).reverse := by
  simp only [PlanarPresentation.incidenceSegmentOrigins,
    ↓reduceIte, List.map_map]
  rw [List.map_reverse]
  change
    ((gridPolylineSegments
      (presentation.incidenceRoute tag)).zipIdx.map
        (fun item => (item.1.translate
          (presentation.drawing.periodTranslation
            latticeShift)).reverse)).reverse = _
  congr 1
  simpa using
    map_zipIdx_value
      (gridPolylineSegments
        (presentation.incidenceRoute tag))
      (fun segment =>
        (segment.translate
          (presentation.drawing.periodTranslation
            latticeShift)).reverse)

/-- The translated reverse of the second incidence meets the end of the
first incidence at their common colored element. -/
theorem PlanarPresentation.throughIncidenceRoutes_boundary
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (color : WireColor) (atom : Nat)
    {first second : Incidence}
    (firstMember : first ∈ problem.incidences color atom)
    (secondMember : second ∈ problem.incidences color atom) :
    (presentation.incidenceRoute
        ⟨first.tripleIndex, color⟩).getLast? =
      (presentation.reversedIncidenceRouteAt
        color first second).head? := by
  have firstEndpoints :=
    presentation.incidenceRoute_endpoints_of_incidence
      color atom firstMember
  have secondEndpoints :=
    presentation.incidenceRoute_endpoints_of_incidence
      color atom secondMember
  rw [firstEndpoints.2]
  simp only [PlanarPresentation.reversedIncidenceRouteAt,
    List.head?_reverse, translatePolyline,
    List.getLast?_map, secondEndpoints.2, Option.map_some]
  simpa using
    congrArg some
      (periodTranslation_element_endpoint_sub
        presentation.drawing
        (presentation.drawing.vertexPosition
          problem.incidenceGraph (.element color atom))
        first.offset second.offset).symm

/-- Segment origins realize exactly the segment list of one contracted
route.  Thus contraction neither creates nor geometrically alters a segment
except for periodic translation and traversal reversal. -/
theorem PlanarPresentation.contractedEdgeRoute_segments
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (color : WireColor) (atom : Nat)
    {edge : ContractedEdge}
    (member :
      edge ∈ problem.contractedEdgesForElement color atom) :
    gridPolylineSegments
        (presentation.contractedEdgeRoute edge) =
      (presentation.contractedSegmentOrigins edge).map
        (ContractedSegmentOrigin.realize
          presentation.drawing) := by
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
      simp only [PlanarPresentation.contractedEdgeRoute,
        PlanarPresentation.contractedSegmentOrigins,
        ContractedEdge.sourceTag]
      rw [presentation.incidenceSegmentOrigins_realize_false]
      simp [PeriodicGridDrawing.periodTranslation,
        GridSegment.translate, Cell.scale, Cell.add]
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
      let boundary :=
        Cell.add
          (presentation.drawing.vertexPosition
            problem.incidenceGraph
            (.element edgeColor edgeAtom))
          (presentation.drawing.periodTranslation first.offset)
      have firstLast :
          (presentation.incidenceRoute
            ⟨first.tripleIndex, edgeColor⟩).getLast? =
              some boundary := by
        exact
          (presentation.incidenceRoute_endpoints_of_incidence
            edgeColor edgeAtom firstMember).2
      have secondHead :
          (presentation.reversedIncidenceRouteAt
            edgeColor first second).head? = some boundary := by
        rw [← presentation.throughIncidenceRoutes_boundary
          edgeColor edgeAtom firstMember secondMember]
        exact firstLast
      rw [PlanarPresentation.contractedEdgeRoute]
      rw [gridPolylineSegments_joinPolylines
        firstLast secondHead]
      simp only [PlanarPresentation.contractedSegmentOrigins,
        ContractedEdge.sourceTag, ContractedEdge.targetTag,
        List.map_append]
      rw [presentation.incidenceSegmentOrigins_realize_false]
      rw [presentation.incidenceSegmentOrigins_realize_true]
      simp only [PlanarPresentation.reversedIncidenceRouteAt,
        gridPolylineSegments_reverse,
        gridPolylineSegments_translatePolyline]
      apply congrArg₂ (· ++ ·)
      · simp [PeriodicGridDrawing.periodTranslation,
          GridSegment.translate, Cell.scale, Cell.add]
      · rw [List.map_reverse, List.map_map]
        simp [Function.comp_def]

/-- A genuine incidence route occurs at its stable tag index in the original
drawing's indexed route list. -/
theorem PlanarPresentation.incidenceRoute_zipIdx_mem
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    {tag : IncidenceTag}
    (member : tag ∈ problem.incidenceTags) :
    (presentation.incidenceRoute tag,
        problem.incidenceRouteIndex tag) ∈
      presentation.drawing.edgeRoutes.zipIdx := by
  rw [List.mem_zipIdx_iff_getElem?,
    List.getElem?_eq_some_iff]
  have indexLt :
      problem.incidenceRouteIndex tag <
        presentation.drawing.edgeRoutes.length := by
    rw [presentation.compatible.2.2.1,
      incidenceGraph_edges_length]
    exact List.idxOf_lt_length_iff.mpr member
  refine ⟨indexLt, ?_⟩
  unfold PlanarPresentation.incidenceRoute
    PeriodicGridDrawing.edgeRoute
  rw [List.getD_eq_getElem _ _ indexLt]

/-- Every provenance record from one genuine incidence block names an actual
indexed segment of the original drawing. -/
theorem PlanarPresentation.incidenceSegmentOrigin_original_mem
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    {tag : IncidenceTag}
    (tagMember : tag ∈ problem.incidenceTags)
    (latticeShift : Cell) (reversed : Bool)
    {origin : ContractedSegmentOrigin}
    (originMember :
      origin ∈ presentation.incidenceSegmentOrigins
        tag latticeShift reversed) :
    origin.original ∈ presentation.drawing.indexedSegments := by
  unfold PlanarPresentation.incidenceSegmentOrigins at originMember
  split at originMember
  next isReversed =>
    simp only [List.mem_map] at originMember
    rcases originMember with ⟨tagged, taggedMember, rfl⟩
    have taggedMember' :
        tagged ∈
          (gridPolylineSegments
            (presentation.incidenceRoute tag)).zipIdx := by
      simpa using taggedMember
    unfold PeriodicGridDrawing.indexedSegments
    apply List.mem_flatMap.mpr
    refine
      ⟨(presentation.incidenceRoute tag,
          problem.incidenceRouteIndex tag),
        presentation.incidenceRoute_zipIdx_mem tagMember, ?_⟩
    apply List.mem_map.mpr
    exact ⟨tagged, taggedMember', rfl⟩
  next notReversed =>
    simp only [List.mem_map] at originMember
    rcases originMember with ⟨tagged, taggedMember, rfl⟩
    unfold PeriodicGridDrawing.indexedSegments
    apply List.mem_flatMap.mpr
    refine
      ⟨(presentation.incidenceRoute tag,
          problem.incidenceRouteIndex tag),
        presentation.incidenceRoute_zipIdx_mem tagMember, ?_⟩
    apply List.mem_map.mpr
    exact ⟨tagged, taggedMember, rfl⟩

/-- An incidence-origin block records its defining tag, stable route index,
translation, and traversal direction literally. -/
theorem PlanarPresentation.incidenceSegmentOrigin_metadata
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (tag : IncidenceTag) (latticeShift : Cell) (reversed : Bool)
    {origin : ContractedSegmentOrigin}
    (originMember :
      origin ∈ presentation.incidenceSegmentOrigins
        tag latticeShift reversed) :
    origin.tag = tag ∧
      origin.original.routeIndex =
        problem.incidenceRouteIndex tag ∧
      origin.latticeShift = latticeShift ∧
      origin.reversed = reversed := by
  unfold PlanarPresentation.incidenceSegmentOrigins at originMember
  split at originMember <;>
    simp only [List.mem_map] at originMember <;>
    rcases originMember with ⟨tagged, taggedMember, rfl⟩ <;>
    exact ⟨rfl, rfl, rfl, rfl⟩

/-- Every segment origin attached to an executable contracted edge names an
actual segment of the original planar drawing. -/
theorem PlanarPresentation.contractedSegmentOrigin_original_mem
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    {edge : ContractedEdge}
    (edgeMember : edge ∈ problem.contractedEdges)
    {origin : ContractedSegmentOrigin}
    (originMember :
      origin ∈ presentation.contractedSegmentOrigins edge) :
    origin.original ∈ presentation.drawing.indexedSegments := by
  cases edge with
  | retained color atom incidence =>
      have tagMember :
          (⟨incidence.tripleIndex, color⟩ : IncidenceTag) ∈
            problem.incidenceTags := by
        apply incidenceTag_mem_of_contractedEdge problem edgeMember
        simp [ContractedEdge.incidenceTags,
          ContractedEdge.sourceTag]
      change
        origin ∈ presentation.incidenceSegmentOrigins
          (⟨incidence.tripleIndex, color⟩ : IncidenceTag)
          (0, 0) false at originMember
      exact
        presentation.incidenceSegmentOrigin_original_mem
          (tag := ⟨incidence.tripleIndex, color⟩)
          tagMember (0, 0) false
          originMember
  | through color atom first second =>
      simp only [PlanarPresentation.contractedSegmentOrigins,
        List.mem_append] at originMember
      rcases originMember with sourceMember | targetMember
      · have tagMember :
            (⟨first.tripleIndex, color⟩ : IncidenceTag) ∈
              problem.incidenceTags := by
          apply incidenceTag_mem_of_contractedEdge problem edgeMember
          simp [ContractedEdge.incidenceTags,
            ContractedEdge.sourceTag]
        exact
          presentation.incidenceSegmentOrigin_original_mem
            (tag := ⟨first.tripleIndex, color⟩)
            tagMember (0, 0) false sourceMember
      · have tagMember :
            (⟨second.tripleIndex, color⟩ : IncidenceTag) ∈
              problem.incidenceTags := by
          apply incidenceTag_mem_of_contractedEdge problem edgeMember
          simp [ContractedEdge.incidenceTags,
            ContractedEdge.targetTag]
        exact
          presentation.incidenceSegmentOrigin_original_mem
            (tag := ⟨second.tripleIndex, color⟩)
            tagMember (Cell.sub first.offset second.offset)
            true targetMember

/-- A contracted segment origin's tag is one of the original incidences
stored by its owning contracted edge. -/
theorem PlanarPresentation.contractedSegmentOrigin_tag_mem
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (edge : ContractedEdge)
    {origin : ContractedSegmentOrigin}
    (originMember :
      origin ∈ presentation.contractedSegmentOrigins edge) :
    origin.tag ∈ edge.incidenceTags := by
  cases edge with
  | retained color atom incidence =>
      have metadata :=
        presentation.incidenceSegmentOrigin_metadata
          (⟨incidence.tripleIndex, color⟩ : IncidenceTag)
          (0, 0) false originMember
      simp [ContractedEdge.incidenceTags,
        ContractedEdge.sourceTag, metadata.1]
  | through color atom first second =>
      simp only [PlanarPresentation.contractedSegmentOrigins,
        List.mem_append] at originMember
      rcases originMember with sourceMember | targetMember
      · have metadata :=
          presentation.incidenceSegmentOrigin_metadata
            (⟨first.tripleIndex, color⟩ : IncidenceTag)
            (0, 0) false sourceMember
        simp [ContractedEdge.incidenceTags,
          ContractedEdge.sourceTag, metadata.1]
      · have metadata :=
          presentation.incidenceSegmentOrigin_metadata
            (⟨second.tripleIndex, color⟩ : IncidenceTag)
            (Cell.sub first.offset second.offset)
            true targetMember
        simp [ContractedEdge.incidenceTags,
          ContractedEdge.targetTag, metadata.1]

/-- The original route index recorded by any contracted segment origin is
the stable index of its recorded incidence tag. -/
theorem PlanarPresentation.contractedSegmentOrigin_routeIndex
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (edge : ContractedEdge)
    {origin : ContractedSegmentOrigin}
    (originMember :
      origin ∈ presentation.contractedSegmentOrigins edge) :
    origin.original.routeIndex =
      problem.incidenceRouteIndex origin.tag := by
  cases edge with
  | retained color atom incidence =>
      have metadata :=
        presentation.incidenceSegmentOrigin_metadata
          (⟨incidence.tripleIndex, color⟩ : IncidenceTag)
          (0, 0) false originMember
      rw [metadata.1, metadata.2.1]
  | through color atom first second =>
      simp only [PlanarPresentation.contractedSegmentOrigins,
        List.mem_append] at originMember
      rcases originMember with sourceMember | targetMember
      · have metadata :=
          presentation.incidenceSegmentOrigin_metadata
            (⟨first.tripleIndex, color⟩ : IncidenceTag)
            (0, 0) false sourceMember
        rw [metadata.1, metadata.2.1]
      · have metadata :=
          presentation.incidenceSegmentOrigin_metadata
            (⟨second.tripleIndex, color⟩ : IncidenceTag)
            (Cell.sub first.offset second.offset)
            true targetMember
        rw [metadata.1, metadata.2.1]

/-- If every block is nonempty, a duplicate-free flattening can only come
from a duplicate-free outer list. -/
theorem nodup_of_flatMap_nodup_of_blocks_ne_nil
    {α β : Type*} (values : List α) (blocks : α → List β)
    (flattenedNodup : (values.flatMap blocks).Nodup)
    (blocksNonempty : ∀ value ∈ values, blocks value ≠ []) :
    values.Nodup := by
  induction values with
  | nil => exact List.nodup_nil
  | cons head tail induction =>
      simp only [List.flatMap_cons] at flattenedNodup
      have parts := List.nodup_append.mp flattenedNodup
      rw [List.nodup_cons]
      constructor
      · intro headMember
        have headNonempty :
            blocks head ≠ [] :=
          blocksNonempty head List.mem_cons_self
        obtain ⟨item, itemMember⟩ :=
          (blocks head).exists_mem_of_ne_nil headNonempty
        have tailMember :
            item ∈ tail.flatMap blocks := by
          apply List.mem_flatMap.mpr
          exact ⟨head, headMember, itemMember⟩
        exact
          (parts.2.2 item itemMember item tailMember) rfl
      · apply induction parts.2.1
        intro value valueMember
        exact blocksNonempty value
          (List.mem_cons_of_mem head valueMember)

/-- Executable contracted edges are duplicate-free under the degree
promise.  Each edge owns at least one incidence tag, and the flattened tag
list is already known to be duplicate-free. -/
theorem contractedEdges_nodup
    (problem : PeriodicThreeDM)
    (degreeTwoOrThree : problem.DegreeTwoOrThree) :
    problem.contractedEdges.Nodup := by
  apply nodup_of_flatMap_nodup_of_blocks_ne_nil
    problem.contractedEdges ContractedEdge.incidenceTags
    (contractedIncidenceTags_nodup
      problem degreeTwoOrThree)
  intro edge edgeMember
  cases edge <;> simp [ContractedEdge.incidenceTags]

/-- Two contracted edges sharing an original incidence tag are the same
edge. -/
theorem contractedEdges_eq_of_common_incidenceTag
    (problem : PeriodicThreeDM)
    (degreeTwoOrThree : problem.DegreeTwoOrThree)
    {first second : ContractedEdge}
    (firstMember : first ∈ problem.contractedEdges)
    (secondMember : second ∈ problem.contractedEdges)
    {tag : IncidenceTag}
    (firstTag : tag ∈ first.incidenceTags)
    (secondTag : tag ∈ second.incidenceTags) :
    first = second := by
  by_contra different
  have flattenedNodup :=
    contractedIncidenceTags_nodup
      problem degreeTwoOrThree
  have blocksPairwise :=
    (List.nodup_flatMap.mp flattenedNodup).2
  letI :
      Std.Symm
        (Function.onFun List.Disjoint
          ContractedEdge.incidenceTags) :=
    ⟨fun _ _ disjoint => disjoint.symm⟩
  have disjoint :=
    blocksPairwise.forall firstMember secondMember different
  exact (List.disjoint_left.mp disjoint)
    firstTag secondTag

/-- Equality of original route indices forces equality of the incidence tags
recorded by contracted segment origins. -/
theorem PlanarPresentation.contractedSegmentOrigins_tag_eq_of_routeIndex_eq
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (firstEdge secondEdge : ContractedEdge)
    {firstOrigin secondOrigin : ContractedSegmentOrigin}
    (firstMember :
      firstOrigin ∈
        presentation.contractedSegmentOrigins firstEdge)
    (secondMember :
      secondOrigin ∈
        presentation.contractedSegmentOrigins secondEdge)
    (routeIndexEq :
      firstOrigin.original.routeIndex =
        secondOrigin.original.routeIndex)
    (firstTagOriginal :
      firstOrigin.tag ∈ problem.incidenceTags) :
    firstOrigin.tag = secondOrigin.tag := by
  rw [presentation.contractedSegmentOrigin_routeIndex
      firstEdge firstMember,
    presentation.contractedSegmentOrigin_routeIndex
      secondEdge secondMember] at routeIndexEq
  exact
    (List.idxOf_inj firstTagOriginal).mp routeIndexEq

/-- Within one incidence block, the original indexed segment uniquely
determines the complete provenance record. -/
theorem PlanarPresentation.incidenceSegmentOrigins_injective_original
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (tag : IncidenceTag) (latticeShift : Cell) (reversed : Bool)
    {first second : ContractedSegmentOrigin}
    (firstMember :
      first ∈ presentation.incidenceSegmentOrigins
        tag latticeShift reversed)
    (secondMember :
      second ∈ presentation.incidenceSegmentOrigins
        tag latticeShift reversed)
    (originalEq : first.original = second.original) :
    first = second := by
  unfold PlanarPresentation.incidenceSegmentOrigins at firstMember
  unfold PlanarPresentation.incidenceSegmentOrigins at secondMember
  split at firstMember <;>
    simp only [List.mem_map] at firstMember secondMember <;>
    rcases firstMember with
      ⟨⟨firstSegment, firstIndex⟩, firstTaggedMember, rfl⟩ <;>
    rcases secondMember with
      ⟨⟨secondSegment, secondIndex⟩, secondTaggedMember, rfl⟩ <;>
    simp only [IndexedGridSegment.mk.injEq] at originalEq <;>
    rcases originalEq with
      ⟨indexEq, indexAndSegmentEq⟩ <;>
    rcases indexAndSegmentEq with
      ⟨rfl, rfl⟩ <;>
    rfl

/-- Every incidence-origin block is duplicate-free because the within-route
segment index is recorded in each provenance value. -/
theorem PlanarPresentation.incidenceSegmentOrigins_nodup
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (tag : IncidenceTag) (latticeShift : Cell) (reversed : Bool) :
    (presentation.incidenceSegmentOrigins
      tag latticeShift reversed).Nodup := by
  let tagged :=
    (gridPolylineSegments
      (presentation.incidenceRoute tag)).zipIdx
  have taggedNodup : tagged.Nodup :=
    List.Nodup.of_map Prod.snd
      (List.nodup_zipIdx_map_snd
        (gridPolylineSegments
          (presentation.incidenceRoute tag)))
  unfold PlanarPresentation.incidenceSegmentOrigins
  change
    ((if reversed then tagged.reverse else tagged).map
      (fun item =>
        (⟨⟨problem.incidenceRouteIndex tag, item.2, item.1⟩,
          tag, latticeShift, reversed⟩ :
            ContractedSegmentOrigin))).Nodup
  have orderedNodup :
      (if reversed then tagged.reverse else tagged).Nodup := by
    by_cases isReversed : reversed = true
    · simp [isReversed, taggedNodup]
    · simp [isReversed, taggedNodup]
  apply orderedNodup.map
  intro first second equality
  rcases first with ⟨firstSegment, firstIndex⟩
  rcases second with ⟨secondSegment, secondIndex⟩
  have originalEq :=
    congrArg ContractedSegmentOrigin.original equality
  simp only [IndexedGridSegment.mk.injEq] at originalEq
  rcases originalEq with ⟨routeEq, indexEq, segmentEq⟩
  subst secondIndex
  subst secondSegment
  rfl

/-- Within one executable contracted edge, no two provenance records name
the same original indexed segment. -/
theorem PlanarPresentation.contractedSegmentOrigins_injective_original
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (degreeTwoOrThree : problem.DegreeTwoOrThree)
    {edge : ContractedEdge}
    (edgeMember : edge ∈ problem.contractedEdges)
    {first second : ContractedSegmentOrigin}
    (firstMember :
      first ∈ presentation.contractedSegmentOrigins edge)
    (secondMember :
      second ∈ presentation.contractedSegmentOrigins edge)
    (originalEq : first.original = second.original) :
    first = second := by
  cases edge with
  | retained color atom incidence =>
      exact
        presentation.incidenceSegmentOrigins_injective_original
          (⟨incidence.tripleIndex, color⟩ : IncidenceTag)
          (0, 0) false firstMember secondMember originalEq
  | through color atom firstIncidence secondIncidence =>
      simp only [PlanarPresentation.contractedSegmentOrigins,
        List.mem_append] at firstMember secondMember
      rcases firstMember with
          firstSource | firstTarget <;>
        rcases secondMember with
          secondSource | secondTarget
      · exact
          presentation.incidenceSegmentOrigins_injective_original
            (⟨firstIncidence.tripleIndex, color⟩ : IncidenceTag)
            (0, 0) false firstSource secondSource originalEq
      · have firstMetadata :=
          presentation.incidenceSegmentOrigin_metadata
            (⟨firstIncidence.tripleIndex, color⟩ : IncidenceTag)
            (0, 0) false firstSource
        have secondMetadata :=
          presentation.incidenceSegmentOrigin_metadata
            (⟨secondIncidence.tripleIndex, color⟩ : IncidenceTag)
            (Cell.sub firstIncidence.offset secondIncidence.offset)
            true secondTarget
        have firstTagOriginal :
            first.tag ∈ problem.incidenceTags := by
          apply incidenceTag_mem_of_contractedEdge problem edgeMember
          simp [ContractedEdge.incidenceTags,
            ContractedEdge.sourceTag, firstMetadata.1]
        have routeEq :=
          congrArg IndexedGridSegment.routeIndex originalEq
        rw [firstMetadata.2.1, secondMetadata.2.1] at routeEq
        rw [firstMetadata.1] at firstTagOriginal
        have knownTagEq :
            (⟨firstIncidence.tripleIndex, color⟩ : IncidenceTag) =
              ⟨secondIncidence.tripleIndex, color⟩ :=
          (List.idxOf_inj firstTagOriginal).mp routeEq
        have tagEq :
            first.tag = second.tag :=
          firstMetadata.1.trans
            (knownTagEq.trans secondMetadata.1.symm)
        rw [firstMetadata.1, secondMetadata.1] at tagEq
        have localNodup :
            (ContractedEdge.through color atom
              firstIncidence secondIncidence).incidenceTags.Nodup :=
          (List.nodup_flatMap.mp
            (contractedIncidenceTags_nodup
              problem degreeTwoOrThree)).1
            _ edgeMember
        simp [ContractedEdge.incidenceTags,
          ContractedEdge.sourceTag,
          ContractedEdge.targetTag, tagEq] at localNodup
      · have firstMetadata :=
          presentation.incidenceSegmentOrigin_metadata
            (⟨secondIncidence.tripleIndex, color⟩ : IncidenceTag)
            (Cell.sub firstIncidence.offset secondIncidence.offset)
            true firstTarget
        have secondMetadata :=
          presentation.incidenceSegmentOrigin_metadata
            (⟨firstIncidence.tripleIndex, color⟩ : IncidenceTag)
            (0, 0) false secondSource
        have firstTagOriginal :
            first.tag ∈ problem.incidenceTags := by
          apply incidenceTag_mem_of_contractedEdge problem edgeMember
          simp [ContractedEdge.incidenceTags,
            ContractedEdge.targetTag, firstMetadata.1]
        have routeEq :=
          congrArg IndexedGridSegment.routeIndex originalEq
        rw [firstMetadata.2.1, secondMetadata.2.1] at routeEq
        rw [firstMetadata.1] at firstTagOriginal
        have knownTagEq :
            (⟨secondIncidence.tripleIndex, color⟩ : IncidenceTag) =
              ⟨firstIncidence.tripleIndex, color⟩ :=
          (List.idxOf_inj firstTagOriginal).mp routeEq
        have tagEq :
            first.tag = second.tag :=
          firstMetadata.1.trans
            (knownTagEq.trans secondMetadata.1.symm)
        rw [firstMetadata.1, secondMetadata.1] at tagEq
        have localNodup :
            (ContractedEdge.through color atom
              firstIncidence secondIncidence).incidenceTags.Nodup :=
          (List.nodup_flatMap.mp
            (contractedIncidenceTags_nodup
              problem degreeTwoOrThree)).1
            _ edgeMember
        simp [ContractedEdge.incidenceTags,
          ContractedEdge.sourceTag,
          ContractedEdge.targetTag, tagEq] at localNodup
      · exact
          presentation.incidenceSegmentOrigins_injective_original
            (⟨secondIncidence.tripleIndex, color⟩ : IncidenceTag)
            (Cell.sub firstIncidence.offset secondIncidence.offset)
            true firstTarget secondTarget originalEq

/-- Across the complete contracted graph, an original indexed segment has a
unique owning contracted edge. -/
theorem PlanarPresentation.contractedSegmentOrigins_edge_eq_of_original_eq
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (degreeTwoOrThree : problem.DegreeTwoOrThree)
    {firstEdge secondEdge : ContractedEdge}
    (firstEdgeMember : firstEdge ∈ problem.contractedEdges)
    (secondEdgeMember : secondEdge ∈ problem.contractedEdges)
    {firstOrigin secondOrigin : ContractedSegmentOrigin}
    (firstOriginMember :
      firstOrigin ∈
        presentation.contractedSegmentOrigins firstEdge)
    (secondOriginMember :
      secondOrigin ∈
        presentation.contractedSegmentOrigins secondEdge)
    (originalEq :
      firstOrigin.original = secondOrigin.original) :
    firstEdge = secondEdge := by
  have firstTagInEdge :=
    presentation.contractedSegmentOrigin_tag_mem
      firstEdge firstOriginMember
  have secondTagInEdge :=
    presentation.contractedSegmentOrigin_tag_mem
      secondEdge secondOriginMember
  have firstTagOriginal :
      firstOrigin.tag ∈ problem.incidenceTags :=
    incidenceTag_mem_of_contractedEdge
      problem firstEdgeMember firstTagInEdge
  have tagEq :=
    presentation.contractedSegmentOrigins_tag_eq_of_routeIndex_eq
      firstEdge secondEdge firstOriginMember secondOriginMember
      (congrArg IndexedGridSegment.routeIndex originalEq)
      firstTagOriginal
  exact
    contractedEdges_eq_of_common_incidenceTag
      problem degreeTwoOrThree
      firstEdgeMember secondEdgeMember
      firstTagInEdge (tagEq ▸ secondTagInEdge)

/-- Across the complete contracted graph, the original indexed segment
uniquely determines the full provenance record. -/
theorem PlanarPresentation.contractedSegmentOrigins_global_injective
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (degreeTwoOrThree : problem.DegreeTwoOrThree)
    {firstEdge secondEdge : ContractedEdge}
    (firstEdgeMember : firstEdge ∈ problem.contractedEdges)
    (secondEdgeMember : secondEdge ∈ problem.contractedEdges)
    {firstOrigin secondOrigin : ContractedSegmentOrigin}
    (firstOriginMember :
      firstOrigin ∈
        presentation.contractedSegmentOrigins firstEdge)
    (secondOriginMember :
      secondOrigin ∈
        presentation.contractedSegmentOrigins secondEdge)
    (originalEq :
      firstOrigin.original = secondOrigin.original) :
    firstEdge = secondEdge ∧ firstOrigin = secondOrigin := by
  have edgeEq :=
    presentation.contractedSegmentOrigins_edge_eq_of_original_eq
      degreeTwoOrThree firstEdgeMember secondEdgeMember
      firstOriginMember secondOriginMember originalEq
  subst secondEdge
  exact
    ⟨rfl,
      presentation.contractedSegmentOrigins_injective_original
        degreeTwoOrThree firstEdgeMember
        firstOriginMember secondOriginMember originalEq⟩

/-- The segment-origin list of every executable contracted edge is
duplicate-free. -/
theorem PlanarPresentation.contractedSegmentOrigins_nodup
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (degreeTwoOrThree : problem.DegreeTwoOrThree)
    {edge : ContractedEdge}
    (edgeMember : edge ∈ problem.contractedEdges) :
    (presentation.contractedSegmentOrigins edge).Nodup := by
  cases edge with
  | retained color atom incidence =>
      exact presentation.incidenceSegmentOrigins_nodup
        (⟨incidence.tripleIndex, color⟩ : IncidenceTag)
        (0, 0) false
  | through color atom first second =>
      rw [PlanarPresentation.contractedSegmentOrigins,
        List.nodup_append]
      refine
        ⟨presentation.incidenceSegmentOrigins_nodup
            (⟨first.tripleIndex, color⟩ : IncidenceTag)
            (0, 0) false,
          presentation.incidenceSegmentOrigins_nodup
            (⟨second.tripleIndex, color⟩ : IncidenceTag)
            (Cell.sub first.offset second.offset) true,
          ?_⟩
      intro firstOrigin firstOriginMember
        secondOrigin secondOriginMember equality
      have firstMetadata :=
        presentation.incidenceSegmentOrigin_metadata
          (⟨first.tripleIndex, color⟩ : IncidenceTag)
          (0, 0) false firstOriginMember
      have secondMetadata :=
        presentation.incidenceSegmentOrigin_metadata
          (⟨second.tripleIndex, color⟩ : IncidenceTag)
          (Cell.sub first.offset second.offset)
          true secondOriginMember
      have tagEq :=
        congrArg ContractedSegmentOrigin.tag equality
      rw [firstMetadata.1, secondMetadata.1] at tagEq
      have localNodup :
          (ContractedEdge.through color atom
            first second).incidenceTags.Nodup :=
        (List.nodup_flatMap.mp
          (contractedIncidenceTags_nodup
            problem degreeTwoOrThree)).1
          _ edgeMember
      simp [ContractedEdge.incidenceTags,
        ContractedEdge.sourceTag,
        ContractedEdge.targetTag, tagEq] at localNodup

/-- Every globally emitted contracted edge has the verified segment-origin
decomposition. -/
theorem PlanarPresentation.contractedEdgeRoute_segments_of_mem
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    {edge : ContractedEdge}
    (edgeMember : edge ∈ problem.contractedEdges) :
    gridPolylineSegments
        (presentation.contractedEdgeRoute edge) =
      (presentation.contractedSegmentOrigins edge).map
        (ContractedSegmentOrigin.realize
          presentation.drawing) := by
  simp only [contractedEdges, List.mem_flatMap] at edgeMember
  rcases edgeMember with ⟨color, colorMember, edgeMember⟩
  simp only [contractedEdgesForColor,
    List.mem_flatMap] at edgeMember
  rcases edgeMember with ⟨atom, atomMember, edgeMember⟩
  exact
    presentation.contractedEdgeRoute_segments
      color atom edgeMember

/-- Every contracted indexed segment paired with its original-segment
provenance, in exactly the drawing's route/segment order. -/
def PlanarPresentation.contractedIndexedSegmentOrigins
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) :
    List (IndexedGridSegment × ContractedSegmentOrigin) :=
  problem.contractedEdges.zipIdx.flatMap fun taggedEdge =>
    (presentation.contractedSegmentOrigins
      taggedEdge.1).zipIdx.map fun taggedOrigin =>
        (⟨taggedEdge.2, taggedOrigin.2,
            taggedOrigin.1.realize presentation.drawing⟩,
          taggedOrigin.1)

/-- Forgetting provenance recovers exactly the contracted drawing's indexed
segment list. -/
theorem PlanarPresentation.contractedIndexedSegmentOrigins_map_fst
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) :
    presentation.contractedIndexedSegmentOrigins.map Prod.fst =
      presentation.contractedDrawing.indexedSegments := by
  have routesEq :
      presentation.contractedDrawing.edgeRoutes =
        problem.contractedEdges.map
          presentation.contractedEdgeRoute := by
    unfold PlanarPresentation.contractedDrawing
    calc
      problem.contractedEdges.zipIdx.map
          (fun tagged =>
            presentation.contractedEdgeRoute tagged.1) =
          (problem.contractedEdges.zipIdx.map Prod.fst).map
            presentation.contractedEdgeRoute := by
              rw [List.map_map]
              rfl
      _ = _ := by
        rw [List.zipIdx_map_fst]
  unfold PlanarPresentation.contractedIndexedSegmentOrigins
    PeriodicGridDrawing.indexedSegments
  rw [routesEq]
  rw [List.zipIdx_map]
  simp only [List.map_flatMap, List.flatMap_map,
    List.map_map, Function.comp_def]
  apply List.flatMap_congr
  intro taggedEdge taggedEdgeMember
  rcases taggedEdge with ⟨edge, edgeIndex⟩
  have segments :=
    presentation.contractedEdgeRoute_segments_of_mem
      (List.fst_mem_of_mem_zipIdx taggedEdgeMember)
  simp only [Prod.map, id_eq] at segments ⊢
  rw [segments, List.zipIdx_map]
  simp [List.map_map, Function.comp_def]

/-- In a duplicate-free list, equality of the values in two `zipIdx`
members forces equality of the complete tagged pairs. -/
theorem tagged_eq_of_mem_zipIdx_of_fst_eq_of_nodup
    {α : Type*} {values : List α}
    (valuesNodup : values.Nodup)
    {first second : α × Nat}
    (firstMember : first ∈ values.zipIdx)
    (secondMember : second ∈ values.zipIdx)
    (valuesEq : first.1 = second.1) :
    first = second := by
  let firstIndex : Fin values.length :=
    ⟨first.2, List.snd_lt_of_mem_zipIdx firstMember⟩
  let secondIndex : Fin values.length :=
    ⟨second.2, List.snd_lt_of_mem_zipIdx secondMember⟩
  have firstAt :
      values.get firstIndex = first.1 := by
    simpa [firstIndex] using
      (List.mem_zipIdx' firstMember).2.symm
  have secondAt :
      values.get secondIndex = second.1 := by
    simpa [secondIndex] using
      (List.mem_zipIdx' secondMember).2.symm
  have getEq :
      values.get firstIndex =
        values.get secondIndex := by
    rw [firstAt, secondAt, valuesEq]
  have indexEq : firstIndex = secondIndex :=
    valuesNodup.get_inj_iff.mp getEq
  apply Prod.ext
  · exact valuesEq
  · exact congrArg Fin.val indexEq

/-- The numeric index in two `zipIdx` members uniquely determines the
complete tagged pair. -/
theorem tagged_eq_of_mem_zipIdx_of_snd_eq'
    {α : Type*} {values : List α}
    {first second : α × Nat}
    (firstMember : first ∈ values.zipIdx)
    (secondMember : second ∈ values.zipIdx)
    (indicesEq : first.2 = second.2) :
    first = second := by
  apply Prod.ext
  · have firstAt :=
      (List.mem_zipIdx_iff_getElem?).mp firstMember
    have secondAt :=
      (List.mem_zipIdx_iff_getElem?).mp secondMember
    rw [indicesEq, secondAt] at firstAt
    exact Option.some.inj firstAt.symm
  · exact indicesEq

/-- Route and within-route indices uniquely identify an indexed segment of
any drawing. -/
theorem indexedSegment_eq_of_indices_eq
    (drawing : PeriodicGridDrawing)
    {first second : IndexedGridSegment}
    (firstMember : first ∈ drawing.indexedSegments)
    (secondMember : second ∈ drawing.indexedSegments)
    (routeIndexEq : first.routeIndex = second.routeIndex)
    (segmentIndexEq : first.segmentIndex = second.segmentIndex) :
    first = second := by
  unfold PeriodicGridDrawing.indexedSegments at firstMember
  unfold PeriodicGridDrawing.indexedSegments at secondMember
  rcases List.mem_flatMap.mp firstMember with
    ⟨firstRoute, firstRouteMember, firstMember⟩
  rcases List.mem_map.mp firstMember with
    ⟨firstSegment, firstSegmentMember, firstEq⟩
  rcases List.mem_flatMap.mp secondMember with
    ⟨secondRoute, secondRouteMember, secondMember⟩
  rcases List.mem_map.mp secondMember with
    ⟨secondSegment, secondSegmentMember, secondEq⟩
  subst first
  subst second
  have routeEq :=
    tagged_eq_of_mem_zipIdx_of_snd_eq'
      firstRouteMember secondRouteMember routeIndexEq
  subst secondRoute
  have segmentEq :=
    tagged_eq_of_mem_zipIdx_of_snd_eq'
      firstSegmentMember secondSegmentMember
      segmentIndexEq
  subst secondSegment
  rfl

/-- Every indexed segment of the contracted drawing has an owning edge and
an origin at the same two list indices. -/
theorem PlanarPresentation.contractedIndexedSegment_has_origin
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    {indexed : IndexedGridSegment}
    (indexedMember :
      indexed ∈
        presentation.contractedDrawing.indexedSegments) :
    ∃ taggedEdge : ContractedEdge × Nat,
      ∃ taggedOrigin : ContractedSegmentOrigin × Nat,
        taggedEdge ∈ problem.contractedEdges.zipIdx ∧
          taggedOrigin ∈
            (presentation.contractedSegmentOrigins
              taggedEdge.1).zipIdx ∧
          indexed =
            ⟨taggedEdge.2, taggedOrigin.2,
              taggedOrigin.1.realize
                presentation.drawing⟩ := by
  have provenanceMember :
      indexed ∈
        presentation.contractedIndexedSegmentOrigins.map
          Prod.fst := by
    rw [presentation.contractedIndexedSegmentOrigins_map_fst]
    exact indexedMember
  rcases List.mem_map.mp provenanceMember with
    ⟨pair, pairMember, pairValueEq⟩
  unfold PlanarPresentation.contractedIndexedSegmentOrigins at pairMember
  rcases List.mem_flatMap.mp pairMember with
    ⟨taggedEdge, taggedEdgeMember, pairMember⟩
  rcases List.mem_map.mp pairMember with
    ⟨taggedOrigin, taggedOriginMember, pairEq⟩
  subst pair
  exact
    ⟨taggedEdge, taggedOrigin,
      taggedEdgeMember, taggedOriginMember,
      pairValueEq.symm⟩

/-- If two contracted segment occurrences induce the same original segment
occurrence (including the provenance translation), then their contracted
occurrence keys were already equal. -/
theorem PlanarPresentation.contractedOccurrenceKey_eq_of_originKey_eq
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (degreeTwoOrThree : problem.DegreeTwoOrThree)
    {firstIndexed secondIndexed : IndexedGridSegment}
    {firstTaggedEdge secondTaggedEdge : ContractedEdge × Nat}
    {firstTaggedOrigin secondTaggedOrigin :
      ContractedSegmentOrigin × Nat}
    (firstEdgeMember :
      firstTaggedEdge ∈ problem.contractedEdges.zipIdx)
    (secondEdgeMember :
      secondTaggedEdge ∈ problem.contractedEdges.zipIdx)
    (firstOriginMember :
      firstTaggedOrigin ∈
        (presentation.contractedSegmentOrigins
          firstTaggedEdge.1).zipIdx)
    (secondOriginMember :
      secondTaggedOrigin ∈
        (presentation.contractedSegmentOrigins
          secondTaggedEdge.1).zipIdx)
    (firstIndexedEq :
      firstIndexed =
        ⟨firstTaggedEdge.2, firstTaggedOrigin.2,
          firstTaggedOrigin.1.realize
            presentation.drawing⟩)
    (secondIndexedEq :
      secondIndexed =
        ⟨secondTaggedEdge.2, secondTaggedOrigin.2,
          secondTaggedOrigin.1.realize
            presentation.drawing⟩)
    (firstTranslate secondTranslate : Cell)
    (originKeyEq :
      PeriodicGridDrawing.SegmentOccurrenceKey
          firstTaggedOrigin.1.original
          (Cell.add firstTaggedOrigin.1.latticeShift
            firstTranslate) =
        PeriodicGridDrawing.SegmentOccurrenceKey
          secondTaggedOrigin.1.original
          (Cell.add secondTaggedOrigin.1.latticeShift
            secondTranslate)) :
    PeriodicGridDrawing.SegmentOccurrenceKey
        firstIndexed firstTranslate =
      PeriodicGridDrawing.SegmentOccurrenceKey
        secondIndexed secondTranslate := by
  simp only [PeriodicGridDrawing.SegmentOccurrenceKey,
    Prod.mk.injEq] at originKeyEq
  rcases originKeyEq with
    ⟨routeIndexEq, segmentIndexEq, translatedEq⟩
  have firstEdgeValueMember :
      firstTaggedEdge.1 ∈ problem.contractedEdges :=
    List.fst_mem_of_mem_zipIdx firstEdgeMember
  have secondEdgeValueMember :
      secondTaggedEdge.1 ∈ problem.contractedEdges :=
    List.fst_mem_of_mem_zipIdx secondEdgeMember
  have firstOriginValueMember :
      firstTaggedOrigin.1 ∈
        presentation.contractedSegmentOrigins
          firstTaggedEdge.1 :=
    List.fst_mem_of_mem_zipIdx firstOriginMember
  have secondOriginValueMember :
      secondTaggedOrigin.1 ∈
        presentation.contractedSegmentOrigins
          secondTaggedEdge.1 :=
    List.fst_mem_of_mem_zipIdx secondOriginMember
  have firstOriginalMember :=
    presentation.contractedSegmentOrigin_original_mem
      firstEdgeValueMember firstOriginValueMember
  have secondOriginalMember :=
    presentation.contractedSegmentOrigin_original_mem
      secondEdgeValueMember secondOriginValueMember
  have originalEq :
      firstTaggedOrigin.1.original =
        secondTaggedOrigin.1.original :=
    indexedSegment_eq_of_indices_eq presentation.drawing
      firstOriginalMember secondOriginalMember
      routeIndexEq segmentIndexEq
  have provenanceEq :=
    presentation.contractedSegmentOrigins_global_injective
      degreeTwoOrThree
      firstEdgeValueMember secondEdgeValueMember
      firstOriginValueMember secondOriginValueMember
      originalEq
  have taggedEdgeEq :
      firstTaggedEdge = secondTaggedEdge :=
    tagged_eq_of_mem_zipIdx_of_fst_eq_of_nodup
      (contractedEdges_nodup problem degreeTwoOrThree)
      firstEdgeMember secondEdgeMember provenanceEq.1
  subst secondTaggedEdge
  have taggedOriginEq :
      firstTaggedOrigin = secondTaggedOrigin :=
    tagged_eq_of_mem_zipIdx_of_fst_eq_of_nodup
      (presentation.contractedSegmentOrigins_nodup
        degreeTwoOrThree firstEdgeValueMember)
      firstOriginMember secondOriginMember provenanceEq.2
  subst secondTaggedOrigin
  have translateEq :
      firstTranslate = secondTranslate := by
    rcases firstTaggedOrigin.1.latticeShift with
      ⟨shiftX, shiftY⟩
    rcases firstTranslate with ⟨firstX, firstY⟩
    rcases secondTranslate with ⟨secondX, secondY⟩
    simp only [Cell.add, Prod.mk.injEq] at translatedEq ⊢
    omega
  subst secondTranslate
  rw [firstIndexedEq, secondIndexedEq]

/-- Period translations respect addition in the graph lattice. -/
theorem periodTranslation_add
    (drawing : PeriodicGridDrawing) (first second : Cell) :
    drawing.periodTranslation (Cell.add first second) =
      Cell.add (drawing.periodTranslation first)
        (drawing.periodTranslation second) := by
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  simp only [PeriodicGridDrawing.periodTranslation,
    Cell.scale, Cell.add, Prod.mk.injEq]
  constructor <;> ring

/-- Successive segment translations combine by vector addition. -/
theorem gridSegment_translate_translate
    (segment : GridSegment) (first second : Cell) :
    (segment.translate first).translate second =
      segment.translate (Cell.add first second) := by
  rcases segment with ⟨start, finish⟩
  rcases start with ⟨startX, startY⟩
  rcases finish with ⟨finishX, finishY⟩
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  simp only [GridSegment.translate, Cell.add]
  congr 1 <;> apply Prod.ext <;> simp <;> ring

/-- Contracting routes does not change the fundamental period. -/
@[simp]
theorem PlanarPresentation.contractedDrawing_periodTranslation
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (translate : Cell) :
    presentation.contractedDrawing.periodTranslation translate =
      presentation.drawing.periodTranslation translate := by
  rfl

/-- Translating a realized contracted segment is the same as translating
its original segment by the sum of its provenance and occurrence shifts,
up to the harmless traversal reversal recorded in the provenance. -/
theorem ContractedSegmentOrigin.realize_translate
    (drawing : PeriodicGridDrawing)
    (origin : ContractedSegmentOrigin)
    (translate : Cell) :
    (origin.realize drawing).translate
        (drawing.periodTranslation translate) =
      let translated :=
        origin.original.segment.translate
          (drawing.periodTranslation
            (Cell.add origin.latticeShift translate))
      if origin.reversed then translated.reverse else translated := by
  cases reversedEq : origin.reversed
  · simp only [ContractedSegmentOrigin.realize, reversedEq,
      Bool.false_eq_true, ↓reduceIte]
    rw [gridSegment_translate_translate,
      periodTranslation_add]
  · simp only [ContractedSegmentOrigin.realize, reversedEq,
      ↓reduceIte]
    rw [← GridSegment.reverse_translate,
      gridSegment_translate_translate,
      periodTranslation_add]

/-- Closed containment of a translated realized segment is exactly closed
containment of its translated original segment. -/
theorem ContractedSegmentOrigin.realize_translate_contains_iff
    (drawing : PeriodicGridDrawing)
    (origin : ContractedSegmentOrigin)
    (translate point : Cell) :
    ((origin.realize drawing).translate
        (drawing.periodTranslation translate)).Contains point ↔
      (origin.original.segment.translate
        (drawing.periodTranslation
          (Cell.add origin.latticeShift translate))).Contains point := by
  rw [origin.realize_translate]
  split
  · simpa only using
      GridSegment.contains_reverse
        (origin.original.segment.translate
          (drawing.periodTranslation
            (Cell.add origin.latticeShift translate)))
        point
  · rfl

/-- Relative-interior containment of a translated realized segment is
exactly relative-interior containment of its translated original segment. -/
theorem ContractedSegmentOrigin.realize_translate_interiorContains_iff
    (drawing : PeriodicGridDrawing)
    (origin : ContractedSegmentOrigin)
    (translate point : Cell) :
    ((origin.realize drawing).translate
        (drawing.periodTranslation translate)).InteriorContains point ↔
      (origin.original.segment.translate
        (drawing.periodTranslation
          (Cell.add origin.latticeShift translate))).InteriorContains
        point := by
  rw [origin.realize_translate]
  split
  · simpa only using
      GridSegment.interiorContains_reverse
        (origin.original.segment.translate
          (drawing.periodTranslation
            (Cell.add origin.latticeShift translate)))
        point
  · rfl

/-- No contracted route segment enters any distinct contracted route
occurrence.  Provenance injectivity turns distinct contracted occurrences
into distinct occurrences of the original planar presentation. -/
theorem PlanarPresentation.contractedDrawing_routesAvoidInteriors
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (degreeTwoOrThree : problem.DegreeTwoOrThree) :
    presentation.contractedDrawing.RoutesAvoidInteriors := by
  intro first firstMember second secondMember
    firstTranslate secondTranslate point keysDifferent
    firstInterior secondContains
  rcases presentation.contractedIndexedSegment_has_origin
      firstMember with
    ⟨firstTaggedEdge, firstTaggedOrigin,
      firstEdgeMember, firstOriginMember, firstIndexedEq⟩
  rcases presentation.contractedIndexedSegment_has_origin
      secondMember with
    ⟨secondTaggedEdge, secondTaggedOrigin,
      secondEdgeMember, secondOriginMember, secondIndexedEq⟩
  have firstEdgeValueMember :
      firstTaggedEdge.1 ∈ problem.contractedEdges :=
    List.fst_mem_of_mem_zipIdx firstEdgeMember
  have secondEdgeValueMember :
      secondTaggedEdge.1 ∈ problem.contractedEdges :=
    List.fst_mem_of_mem_zipIdx secondEdgeMember
  have firstOriginValueMember :
      firstTaggedOrigin.1 ∈
        presentation.contractedSegmentOrigins
          firstTaggedEdge.1 :=
    List.fst_mem_of_mem_zipIdx firstOriginMember
  have secondOriginValueMember :
      secondTaggedOrigin.1 ∈
        presentation.contractedSegmentOrigins
          secondTaggedEdge.1 :=
    List.fst_mem_of_mem_zipIdx secondOriginMember
  have firstOriginalMember :=
    presentation.contractedSegmentOrigin_original_mem
      firstEdgeValueMember firstOriginValueMember
  have secondOriginalMember :=
    presentation.contractedSegmentOrigin_original_mem
      secondEdgeValueMember secondOriginValueMember
  have originKeysDifferent :
      PeriodicGridDrawing.SegmentOccurrenceKey
          firstTaggedOrigin.1.original
          (Cell.add firstTaggedOrigin.1.latticeShift
            firstTranslate) ≠
        PeriodicGridDrawing.SegmentOccurrenceKey
          secondTaggedOrigin.1.original
          (Cell.add secondTaggedOrigin.1.latticeShift
            secondTranslate) := by
    intro originKeysEqual
    exact keysDifferent
      (presentation.contractedOccurrenceKey_eq_of_originKey_eq
        degreeTwoOrThree
        firstEdgeMember secondEdgeMember
        firstOriginMember secondOriginMember
        firstIndexedEq secondIndexedEq
        firstTranslate secondTranslate originKeysEqual)
  have firstRealizedInterior :
      ((firstTaggedOrigin.1.realize presentation.drawing).translate
        (presentation.drawing.periodTranslation
          firstTranslate)).InteriorContains point := by
    rw [firstIndexedEq] at firstInterior
    simpa using firstInterior
  have secondRealizedContains :
      ((secondTaggedOrigin.1.realize presentation.drawing).translate
        (presentation.drawing.periodTranslation
          secondTranslate)).Contains point := by
    rw [secondIndexedEq] at secondContains
    simpa using secondContains
  have firstOriginalInterior :
      (firstTaggedOrigin.1.original.segment.translate
        (presentation.drawing.periodTranslation
          (Cell.add firstTaggedOrigin.1.latticeShift
            firstTranslate))).InteriorContains point :=
    (firstTaggedOrigin.1.realize_translate_interiorContains_iff
      presentation.drawing firstTranslate point).mp
      firstRealizedInterior
  have secondOriginalContains :
      (secondTaggedOrigin.1.original.segment.translate
        (presentation.drawing.periodTranslation
          (Cell.add secondTaggedOrigin.1.latticeShift
            secondTranslate))).Contains point :=
    (secondTaggedOrigin.1.realize_translate_contains_iff
      presentation.drawing secondTranslate point).mp
      secondRealizedContains
  exact
    (presentation.planar.1
      firstTaggedOrigin.1.original firstOriginalMember
      secondTaggedOrigin.1.original secondOriginalMember
      (Cell.add firstTaggedOrigin.1.latticeShift firstTranslate)
      (Cell.add secondTaggedOrigin.1.latticeShift secondTranslate)
      point originKeysDifferent firstOriginalInterior)
      secondOriginalContains

/-- Contracted vertices remain clear of contracted route interiors because
both are inherited from the original planar presentation. -/
theorem PlanarPresentation.contractedDrawing_verticesAvoidRouteInteriors
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) :
    presentation.contractedDrawing.VerticesAvoidRouteInteriors := by
  intro vertexPosition vertexPositionMember
    indexed indexedMember vertexTranslate routeTranslate
    interiorContains
  change vertexPosition ∈
    presentation.contractedVertexPositions at vertexPositionMember
  rw [presentation.contractedVertexPositions_eq_map] at vertexPositionMember
  rcases List.mem_map.mp vertexPositionMember with
    ⟨vertex, vertexMember, vertexPositionEq⟩
  subst vertexPosition
  have originalVertexMember :=
    contractedGraph_vertex_mem_incidenceGraph
      problem vertexMember
  have originalPositionMember :=
    presentation.vertexPosition_mem originalVertexMember
  rcases presentation.contractedIndexedSegment_has_origin
      indexedMember with
    ⟨taggedEdge, taggedOrigin, edgeMember,
      originMember, indexedEq⟩
  have edgeValueMember :
      taggedEdge.1 ∈ problem.contractedEdges :=
    List.fst_mem_of_mem_zipIdx edgeMember
  have originValueMember :
      taggedOrigin.1 ∈
        presentation.contractedSegmentOrigins taggedEdge.1 :=
    List.fst_mem_of_mem_zipIdx originMember
  have originalSegmentMember :=
    presentation.contractedSegmentOrigin_original_mem
      edgeValueMember originValueMember
  have realizedInterior :
      ((taggedOrigin.1.realize presentation.drawing).translate
        (presentation.drawing.periodTranslation
          routeTranslate)).InteriorContains
        (Cell.add
          (presentation.drawing.vertexPosition
            problem.incidenceGraph vertex)
          (presentation.drawing.periodTranslation
            vertexTranslate)) := by
    rw [indexedEq] at interiorContains
    simpa using interiorContains
  have originalInterior :
      (taggedOrigin.1.original.segment.translate
        (presentation.drawing.periodTranslation
          (Cell.add taggedOrigin.1.latticeShift
            routeTranslate))).InteriorContains
        (Cell.add
          (presentation.drawing.vertexPosition
            problem.incidenceGraph vertex)
          (presentation.drawing.periodTranslation
            vertexTranslate)) :=
    (taggedOrigin.1.realize_translate_interiorContains_iff
      presentation.drawing routeTranslate _).mp realizedInterior
  exact
    presentation.planar.2
      (presentation.drawing.vertexPosition
        problem.incidenceGraph vertex)
      originalPositionMember
      taggedOrigin.1.original originalSegmentMember
      vertexTranslate
      (Cell.add taggedOrigin.1.latticeShift routeTranslate)
      originalInterior

/-- Degree-two contraction preserves the complete geometric planarity
predicate. -/
theorem PlanarPresentation.contractedDrawing_isPlanar
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (degreeTwoOrThree : problem.DegreeTwoOrThree) :
    presentation.contractedDrawing.IsPlanar :=
  ⟨presentation.contractedDrawing_routesAvoidInteriors degreeTwoOrThree,
    presentation.contractedDrawing_verticesAvoidRouteInteriors⟩

end PeriodicThreeDM

end LeanTrominoes
