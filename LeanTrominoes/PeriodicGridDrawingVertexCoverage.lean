import LeanTrominoes.PeriodicGridDrawingIndexedSegmentLookup
import LeanTrominoes.PeriodicGridDrawingRouteSimplicity

/-!
# Covering periodic drawing vertices by segment endpoints

For periodic drawings it is useful to separate the combinatorial fact that
every stored graph vertex is an endpoint of some lifted segment from the
geometric fact that routes avoid one another.  The former and orthogonality
turn global route separation into vertex/interior avoidance.
-/

namespace LeanTrominoes
namespace PeriodicGridDrawing

/-- Every stored graph-vertex position is an endpoint of some segment
occurrence in the infinite periodic lift. -/
def VertexPositionsCoveredBySegmentEndpoints
    (drawing : PeriodicGridDrawing) : Prop :=
  ∀ vertexPosition ∈ drawing.vertexPositions,
    ∃ indexed ∈ drawing.indexedSegments,
      ∃ translate : Cell,
        vertexPosition =
            (indexed.segment.translate
              (drawing.periodTranslation translate)).start ∨
          vertexPosition =
            (indexed.segment.translate
              (drawing.periodTranslation translate)).finish

/-- Translating a covered segment occurrence and its endpoint by the same
additional period preserves the endpoint equation. -/
private theorem add_periodTranslation_eq_translated_endpoint
    (drawing : PeriodicGridDrawing)
    (segment : GridSegment)
    (coverTranslate vertexTranslate vertexPosition : Cell)
    (endpoint :
      vertexPosition =
          (segment.translate
            (drawing.periodTranslation coverTranslate)).start ∨
        vertexPosition =
          (segment.translate
            (drawing.periodTranslation coverTranslate)).finish) :
    Cell.add vertexPosition
        (drawing.periodTranslation vertexTranslate) =
          (segment.translate
            (drawing.periodTranslation
              (Cell.add coverTranslate vertexTranslate))).start ∨
      Cell.add vertexPosition
        (drawing.periodTranslation vertexTranslate) =
          (segment.translate
            (drawing.periodTranslation
              (Cell.add coverTranslate vertexTranslate))).finish := by
  rcases segment with ⟨⟨startX, startY⟩, ⟨finishX, finishY⟩⟩
  rcases coverTranslate with ⟨coverX, coverY⟩
  rcases vertexTranslate with ⟨vertexX, vertexY⟩
  rcases vertexPosition with ⟨positionX, positionY⟩
  simp only [GridSegment.translate, PeriodicGridDrawing.periodTranslation,
    Cell.scale, Cell.add, Prod.mk.injEq] at endpoint ⊢
  rcases endpoint with endpoint | endpoint
  · left
    constructor
    · rw [endpoint.1]
      ring
    · rw [endpoint.2]
      ring
  · right
    constructor
    · rw [endpoint.1]
      ring
    · rw [endpoint.2]
      ring

/-- Endpoint coverage converts ordered route separation into the global
vertex/interior avoidance predicate. -/
theorem verticesAvoidRouteInteriors_of_endpointCoverage
    (drawing : PeriodicGridDrawing)
    (covered : drawing.VertexPositionsCoveredBySegmentEndpoints)
    (orthogonal : drawing.IsOrthogonal)
    (routesAvoidInteriors : drawing.RoutesAvoidInteriors) :
    drawing.VerticesAvoidRouteInteriors := by
  intro vertexPosition vertexMember indexed indexedMember
    vertexTranslate routeTranslate interior
  rcases covered vertexPosition vertexMember with
    ⟨covering, coveringMember, coverTranslate, endpoint⟩
  let liftedCoverTranslate : Cell :=
    Cell.add coverTranslate vertexTranslate
  have liftedEndpoint :
      Cell.add vertexPosition
          (drawing.periodTranslation vertexTranslate) =
            (covering.segment.translate
              (drawing.periodTranslation liftedCoverTranslate)).start ∨
        Cell.add vertexPosition
          (drawing.periodTranslation vertexTranslate) =
            (covering.segment.translate
              (drawing.periodTranslation liftedCoverTranslate)).finish := by
    exact
      add_periodTranslation_eq_translated_endpoint
        drawing covering.segment coverTranslate vertexTranslate
        vertexPosition endpoint
  by_cases different :
      SegmentOccurrenceKey indexed routeTranslate ≠
        SegmentOccurrenceKey covering liftedCoverTranslate
  · apply
      routesAvoidInteriors indexed indexedMember
        covering coveringMember routeTranslate liftedCoverTranslate
        (Cell.add vertexPosition
          (drawing.periodTranslation vertexTranslate))
        different interior
    have translatedAligned :
        (covering.segment.translate
          (drawing.periodTranslation liftedCoverTranslate)).IsAxisAligned :=
      (GridSegment.isAxisAligned_translate _ _).mpr
        (orthogonal covering coveringMember)
    rcases liftedEndpoint with endpointStart | endpointFinish
    · rw [endpointStart]
      exact
        GridSegment.contains_start_of_axisAligned translatedAligned
    · rw [endpointFinish]
      exact
        GridSegment.contains_finish_of_axisAligned translatedAligned
  · have keyEq :
        SegmentOccurrenceKey indexed routeTranslate =
          SegmentOccurrenceKey covering liftedCoverTranslate :=
      not_ne_iff.mp different
    have routeIndexEq :
        indexed.routeIndex = covering.routeIndex :=
      congrArg (fun key => key.1) keyEq
    have segmentIndexEq :
        indexed.segmentIndex = covering.segmentIndex :=
      congrArg (fun key => key.2.1) keyEq
    have translateEq :
        routeTranslate = liftedCoverTranslate :=
      congrArg (fun key => key.2.2) keyEq
    have indexedEq : indexed = covering :=
      eq_of_mem_indexedSegments_of_indices_eq
        indexedMember coveringMember routeIndexEq segmentIndexEq
    subst covering
    rw [← translateEq] at liftedEndpoint
    rcases liftedEndpoint with endpointStart | endpointFinish
    · rw [endpointStart] at interior
      exact
        GridSegment.not_interiorContains_start
          (indexed.segment.translate
            (drawing.periodTranslation routeTranslate)) interior
    · rw [endpointFinish] at interior
      exact
        GridSegment.not_interiorContains_finish
          (indexed.segment.translate
            (drawing.periodTranslation routeTranslate)) interior

end PeriodicGridDrawing
end LeanTrominoes
