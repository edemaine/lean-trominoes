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
      latticeShift, reversed⟩

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

end PeriodicThreeDM

end LeanTrominoes
