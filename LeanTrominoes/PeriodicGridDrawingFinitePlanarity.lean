import LeanTrominoes.PeriodicOrthocrossingCrossings
import Mathlib.Data.Int.Range

/-!
# Finite checking of periodic drawing planarity

For drawings whose stored vertices and segment endpoints lie strictly inside
one fundamental square, every possible contact can be translated so that one
participant lies in the canonical square.  The other participant then uses
one of the nine neighboring lattice translations.  Thus the two global
nonintersection predicates reduce to finite Boolean checks.

This interface is intended for the constant-size local gadget drawings used
below.  It separates routine infinite-period arithmetic from the finite
coordinate certificates, which can be discharged by computation.
-/

namespace LeanTrominoes
namespace PeriodicGridDrawing

open PeriodicOrthocrossing

/-- Every stored segment endpoint lies strictly inside the drawing's
fundamental square. -/
def SegmentEndpointsInFundamentalSquare
    (drawing : PeriodicGridDrawing) : Prop :=
  ∀ indexed ∈ drawing.indexedSegments,
    drawing.PositionInFundamentalSquare indexed.segment.start ∧
      drawing.PositionInFundamentalSquare indexed.segment.finish

/-- Integer coordinates in the half-open fundamental interval. -/
def fundamentalCoordinates (drawing : PeriodicGridDrawing) : List Int :=
  (List.range drawing.gridSize).map Int.ofNat

/-- Integer points in the half-open fundamental square. -/
def fundamentalPoints (drawing : PeriodicGridDrawing) : List Cell :=
  drawing.fundamentalCoordinates.flatMap fun horizontal =>
    drawing.fundamentalCoordinates.map fun vertical =>
      (horizontal, vertical)

@[simp]
theorem mem_fundamentalCoordinates_iff
    (drawing : PeriodicGridDrawing) (coordinate : Int) :
    coordinate ∈ drawing.fundamentalCoordinates ↔
      0 ≤ coordinate ∧ coordinate < drawing.gridSize := by
  constructor
  · intro member
    rcases List.mem_map.mp member with
      ⟨index, indexMember, rfl⟩
    exact ⟨Int.natCast_nonneg index,
      Int.ofNat_lt.mpr (List.mem_range.mp indexMember)⟩
  · rintro ⟨nonnegative, upper⟩
    refine List.mem_map.mpr
      ⟨coordinate.toNat, List.mem_range.mpr ?_, ?_⟩
    · rwa [Int.toNat_lt nonnegative]
    · exact Int.toNat_of_nonneg nonnegative

@[simp]
theorem mem_fundamentalPoints_iff
    (drawing : PeriodicGridDrawing) (point : Cell) :
    point ∈ drawing.fundamentalPoints ↔
      0 ≤ point.1 ∧ point.1 < drawing.gridSize ∧
        0 ≤ point.2 ∧ point.2 < drawing.gridSize := by
  rcases point with ⟨horizontal, vertical⟩
  simp [fundamentalPoints, and_assoc]

/-- Normalize a point by the drawing translation of one lattice cell. -/
def normalizePoint (drawing : PeriodicGridDrawing)
    (point translate : Cell) : Cell :=
  Cell.sub point (drawing.periodTranslation translate)

/-- Translating a segment and point by the same integer vector preserves
relative-interior containment. -/
theorem interiorContains_translate_iff
    (segment : GridSegment) (offset point : Cell) :
    (segment.translate offset).InteriorContains
        (Cell.add point offset) ↔
      segment.InteriorContains point := by
  rcases segment with ⟨⟨startX, startY⟩, ⟨finishX, finishY⟩⟩
  rcases offset with ⟨offsetX, offsetY⟩
  rcases point with ⟨pointX, pointY⟩
  simp only [GridSegment.InteriorContains, GridSegment.IsHorizontal,
    GridSegment.IsVertical, GridSegment.StrictlyBetween,
    GridSegment.translate, Cell.add]
  omega

/-- Translating a segment and point by the same integer vector also
preserves closed containment. -/
theorem contains_translate_iff
    (segment : GridSegment) (offset point : Cell) :
    (segment.translate offset).Contains (Cell.add point offset) ↔
      segment.Contains point := by
  rcases segment with ⟨⟨startX, startY⟩, ⟨finishX, finishY⟩⟩
  rcases offset with ⟨offsetX, offsetY⟩
  rcases point with ⟨pointX, pointY⟩
  simp only [GridSegment.Contains, GridSegment.IsHorizontal,
    GridSegment.IsVertical, GridSegment.Between,
    GridSegment.translate, Cell.add]
  omega

/-- Adding back the normalization vector recovers the original point. -/
theorem normalizePoint_add
    (drawing : PeriodicGridDrawing) (point translate : Cell) :
    Cell.add (drawing.normalizePoint point translate)
        (drawing.periodTranslation translate) = point := by
  rcases point with ⟨pointX, pointY⟩
  rcases translate with ⟨translateX, translateY⟩
  simp [normalizePoint, periodTranslation, Cell.add, Cell.sub, Cell.scale]

/-- A relative lattice translation followed by the reference translation is
the original lattice translation. -/
theorem translate_relative
    (drawing : PeriodicGridDrawing) (segment : GridSegment)
    (first second : Cell) :
    (segment.translate
        (drawing.periodTranslation (Cell.sub first second))).translate
          (drawing.periodTranslation second) =
      segment.translate (drawing.periodTranslation first) := by
  rcases segment with ⟨⟨startX, startY⟩, ⟨finishX, finishY⟩⟩
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  simp only [GridSegment.translate, periodTranslation,
    Cell.add, Cell.sub, Cell.scale]
  congr 1 <;> apply Prod.ext <;>
    simp <;>
    ring

/-- Translating both a segment occurrence and its test point by the inverse
of the same lattice vector preserves relative-interior containment. -/
theorem interiorContains_normalize
    (drawing : PeriodicGridDrawing) (segment : GridSegment)
    (firstTranslate secondTranslate point : Cell) :
    (segment.translate
        (drawing.periodTranslation firstTranslate)).InteriorContains point ↔
      (segment.translate
        (drawing.periodTranslation
          (Cell.sub firstTranslate secondTranslate))).InteriorContains
        (drawing.normalizePoint point secondTranslate) := by
  let normalized := drawing.normalizePoint point secondTranslate
  calc
    _ ↔
        ((segment.translate
          (drawing.periodTranslation
            (Cell.sub firstTranslate secondTranslate))).translate
              (drawing.periodTranslation secondTranslate)).InteriorContains
          (Cell.add normalized
            (drawing.periodTranslation secondTranslate)) := by
              rw [translate_relative, normalizePoint_add]
    _ ↔ _ :=
      interiorContains_translate_iff
        (segment.translate
          (drawing.periodTranslation
            (Cell.sub firstTranslate secondTranslate)))
        (drawing.periodTranslation secondTranslate) normalized

/-- The same normalization preserves closed segment containment. -/
theorem contains_normalize
    (drawing : PeriodicGridDrawing) (segment : GridSegment)
    (firstTranslate secondTranslate point : Cell) :
    (segment.translate
        (drawing.periodTranslation firstTranslate)).Contains point ↔
      (segment.translate
        (drawing.periodTranslation
          (Cell.sub firstTranslate secondTranslate))).Contains
        (drawing.normalizePoint point secondTranslate) := by
  let normalized := drawing.normalizePoint point secondTranslate
  calc
    _ ↔
        ((segment.translate
          (drawing.periodTranslation
            (Cell.sub firstTranslate secondTranslate))).translate
              (drawing.periodTranslation secondTranslate)).Contains
          (Cell.add normalized
            (drawing.periodTranslation secondTranslate)) := by
              rw [translate_relative, normalizePoint_add]
    _ ↔ _ :=
      contains_translate_iff
        (segment.translate
          (drawing.periodTranslation
            (Cell.sub firstTranslate secondTranslate)))
        (drawing.periodTranslation secondTranslate) normalized

/-- Closed containment in a segment whose endpoints are in the fundamental
square keeps the contained integer point in the half-open square. -/
theorem fundamental_of_contains
    {drawing : PeriodicGridDrawing} {segment : GridSegment} {point : Cell}
    (startBounds :
      drawing.PositionInFundamentalSquare segment.start)
    (finishBounds :
      drawing.PositionInFundamentalSquare segment.finish)
    (contains : segment.Contains point) :
    point ∈ drawing.fundamentalPoints := by
  rw [mem_fundamentalPoints_iff]
  rcases startBounds with
    ⟨startXLower, startXUpper, startYLower, startYUpper⟩
  rcases finishBounds with
    ⟨finishXLower, finishXUpper, finishYLower, finishYUpper⟩
  rcases contains with
    ⟨horizontal, same, between⟩ |
      ⟨vertical, same, between⟩
  · rcases between with between | between <;>
      simp only [GridSegment.IsHorizontal] at horizontal <;>
      omega
  · rcases between with between | between <;>
      simp only [GridSegment.IsVertical] at vertical <;>
      omega

/-- If two occurrences of fundamental-square segments touch, their relative
lattice translation is one of the nine neighboring translations. -/
theorem relativeTranslate_isNeighbor_of_contact
    {drawing : PeriodicGridDrawing}
    (endpointBounds : drawing.SegmentEndpointsInFundamentalSquare)
    {first second : IndexedGridSegment}
    (firstMember : first ∈ drawing.indexedSegments)
    (secondMember : second ∈ drawing.indexedSegments)
    {firstTranslate secondTranslate point : Cell}
    (firstContains :
      (first.segment.translate
        (drawing.periodTranslation firstTranslate)).InteriorContains point)
    (secondContains :
      (second.segment.translate
        (drawing.periodTranslation secondTranslate)).Contains point) :
    Cell.sub firstTranslate secondTranslate ∈ neighborTranslations := by
  let relative := Cell.sub firstTranslate secondTranslate
  let normalized := drawing.normalizePoint point secondTranslate
  have normalizedFirst :
      (first.segment.translate
        (drawing.periodTranslation relative)).InteriorContains normalized :=
    (interiorContains_normalize drawing first.segment
      firstTranslate secondTranslate point).mp firstContains
  have normalizedSecond : second.segment.Contains normalized := by
    simpa [Cell.sub, periodTranslation, Cell.scale,
      GridSegment.translate, Cell.add] using
      (contains_normalize drawing second.segment
        secondTranslate secondTranslate point).mp secondContains
  have normalizedFundamental :
      normalized ∈ drawing.fundamentalPoints :=
    fundamental_of_contains
      (endpointBounds second secondMember).1
      (endpointBounds second secondMember).2
      normalizedSecond
  have periodPositive : (0 : Int) < drawing.gridSize := by
    exact_mod_cast Nat.zero_lt_succ drawing.gridSizePred
  have firstBounds := endpointBounds first firstMember
  have normalizedBounds :=
    (mem_fundamentalPoints_iff drawing normalized).mp
      normalizedFundamental
  apply (mem_neighborTranslations_iff relative).mpr
  rcases firstBounds with ⟨startBounds, finishBounds⟩
  rcases startBounds with
    ⟨startXLower, startXUpper, startYLower, startYUpper⟩
  rcases finishBounds with
    ⟨finishXLower, finishXUpper, finishYLower, finishYUpper⟩
  rcases normalizedBounds with
    ⟨pointXLower, pointXUpper, pointYLower, pointYUpper⟩
  rcases normalizedFirst with
    ⟨horizontal, same, between⟩ |
      ⟨vertical, same, between⟩
  · have same' :
        normalized.2 =
          first.segment.start.2 +
            drawing.gridSize * relative.2 := by
      simpa [GridSegment.translate, periodTranslation,
        Cell.add, Cell.scale, add_comm] using same
    have between' :
        GridSegment.StrictlyBetween
          (first.segment.start.1 +
            drawing.gridSize * relative.1)
          (first.segment.finish.1 +
            drawing.gridSize * relative.1)
          normalized.1 := by
      simpa [GridSegment.translate, periodTranslation,
        Cell.add, Cell.scale, add_comm] using between
    exact
      ⟨between_shift_is_neighbor periodPositive
          (by omega) (by omega) (by omega) (by omega)
          pointXLower pointXUpper between',
        lane_shift_is_neighbor periodPositive
          (by omega) (by omega)
          pointYLower pointYUpper same'⟩
  · have same' :
        normalized.1 =
          first.segment.start.1 +
            drawing.gridSize * relative.1 := by
      simpa [GridSegment.translate, periodTranslation,
        Cell.add, Cell.scale, add_comm] using same
    have between' :
        GridSegment.StrictlyBetween
          (first.segment.start.2 +
            drawing.gridSize * relative.2)
          (first.segment.finish.2 +
            drawing.gridSize * relative.2)
          normalized.2 := by
      simpa [GridSegment.translate, periodTranslation,
        Cell.add, Cell.scale, add_comm] using between
    exact
      ⟨lane_shift_is_neighbor periodPositive
          (by omega) (by omega)
          pointXLower pointXUpper same',
        between_shift_is_neighbor periodPositive
          (by omega) (by omega) (by omega) (by omega)
          pointYLower pointYUpper between'⟩

/-- Integer coordinates strictly between two endpoints, independent of
their order. -/
def strictlyBetweenCoordinates (first last : Int) : List Int :=
  Int.range (first + 1) last ++ Int.range (last + 1) first

@[simp]
theorem mem_strictlyBetweenCoordinates_iff
    (first last value : Int) :
    value ∈ strictlyBetweenCoordinates first last ↔
      GridSegment.StrictlyBetween first last value := by
  simp [strictlyBetweenCoordinates, Int.mem_range_iff,
    GridSegment.StrictlyBetween]
  omega

/-- All integer points in the relative interior of one horizontal or
vertical segment. -/
def segmentInteriorPoints (segment : GridSegment) : List Cell :=
  (if segment.IsHorizontal then
    (strictlyBetweenCoordinates segment.start.1 segment.finish.1).map
      fun horizontal => (horizontal, segment.start.2)
  else []) ++
  (if segment.IsVertical then
    (strictlyBetweenCoordinates segment.start.2 segment.finish.2).map
      fun vertical => (segment.start.1, vertical)
  else [])

@[simp]
theorem mem_segmentInteriorPoints_iff
    (segment : GridSegment) (point : Cell) :
    point ∈ segmentInteriorPoints segment ↔
      segment.InteriorContains point := by
  rcases segment with ⟨⟨startX, startY⟩, ⟨finishX, finishY⟩⟩
  rcases point with ⟨pointX, pointY⟩
  simp [segmentInteriorPoints, GridSegment.InteriorContains,
    GridSegment.IsHorizontal, GridSegment.IsVertical]
  tauto

/-- Boolean finite check for route-interior avoidance, after fixing the
second occurrence at translate zero. -/
def finiteRoutesAvoidInteriors (drawing : PeriodicGridDrawing) : Bool :=
  drawing.indexedSegments.all fun first =>
    drawing.indexedSegments.all fun second =>
      neighborTranslations.all fun relative =>
        (segmentInteriorPoints
          (first.segment.translate
            (drawing.periodTranslation relative))).all fun point =>
          decide
            (point ∈ drawing.fundamentalPoints →
              SegmentOccurrenceKey first relative ≠
                  SegmentOccurrenceKey second (0, 0) →
                ¬second.segment.Contains point)

/-- Boolean finite check that no stored vertex is in any neighboring route
interior. -/
def finiteVerticesAvoidRouteInteriors
    (drawing : PeriodicGridDrawing) : Bool :=
  drawing.vertexPositions.all fun vertex =>
    drawing.indexedSegments.all fun indexed =>
      neighborTranslations.all fun relative =>
        decide
          (¬(indexed.segment.translate
              (drawing.periodTranslation relative)).InteriorContains vertex)

theorem finiteRoutesAvoidInteriors_spec
    {drawing : PeriodicGridDrawing}
    (checked : drawing.finiteRoutesAvoidInteriors = true) :
    ∀ first ∈ drawing.indexedSegments,
      ∀ second ∈ drawing.indexedSegments,
        ∀ relative ∈ neighborTranslations,
          ∀ point ∈ drawing.fundamentalPoints,
            SegmentOccurrenceKey first relative =
                SegmentOccurrenceKey second (0, 0) ∨
              ¬(first.segment.translate
                  (drawing.periodTranslation relative)).InteriorContains
                point ∨
              ¬second.segment.Contains point := by
  intro first firstMember second secondMember
    relative relativeMember point pointMember
  have raw := checked
  simp only [finiteRoutesAvoidInteriors, List.all_eq_true] at raw
  by_cases contains :
      (first.segment.translate
        (drawing.periodTranslation relative)).InteriorContains point
  · have verdict :=
      raw first firstMember second secondMember relative relativeMember
        point ((mem_segmentInteriorPoints_iff _ _).mpr contains)
    have avoids := (of_decide_eq_true verdict) pointMember
    by_cases same :
        SegmentOccurrenceKey first relative =
          SegmentOccurrenceKey second (0, 0)
    · exact Or.inl same
    · exact Or.inr (Or.inr (avoids same))
  · exact Or.inr (Or.inl contains)

theorem finiteVerticesAvoidRouteInteriors_spec
    {drawing : PeriodicGridDrawing}
    (checked : drawing.finiteVerticesAvoidRouteInteriors = true) :
    ∀ vertex ∈ drawing.vertexPositions,
      ∀ indexed ∈ drawing.indexedSegments,
        ∀ relative ∈ neighborTranslations,
          ¬(indexed.segment.translate
              (drawing.periodTranslation relative)).InteriorContains
            vertex := by
  simpa [finiteVerticesAvoidRouteInteriors] using checked

/-- Subtracting a common lattice translation from two distinct occurrence
keys preserves their distinctness. -/
theorem relative_key_ne
    {first second : IndexedGridSegment}
    {firstTranslate secondTranslate : Cell}
    (different :
      SegmentOccurrenceKey first firstTranslate ≠
        SegmentOccurrenceKey second secondTranslate) :
    SegmentOccurrenceKey first
        (Cell.sub firstTranslate secondTranslate) ≠
      SegmentOccurrenceKey second (0, 0) := by
  intro equal
  apply different
  simp only [SegmentOccurrenceKey] at equal ⊢
  rcases firstTranslate with ⟨firstX, firstY⟩
  rcases secondTranslate with ⟨secondX, secondY⟩
  simp only [Cell.sub, Prod.mk.injEq] at equal ⊢
  omega

/-- The finite neighboring-translation route check proves global periodic
route-interior avoidance. -/
theorem routesAvoidInteriors_of_finite
    {drawing : PeriodicGridDrawing}
    (endpointBounds : drawing.SegmentEndpointsInFundamentalSquare)
    (checked : drawing.finiteRoutesAvoidInteriors = true) :
    drawing.RoutesAvoidInteriors := by
  intro first firstMember second secondMember
    firstTranslate secondTranslate point different
    firstContains secondContains
  let relative := Cell.sub firstTranslate secondTranslate
  let normalized := drawing.normalizePoint point secondTranslate
  have relativeMember :=
    relativeTranslate_isNeighbor_of_contact endpointBounds
      firstMember secondMember firstContains secondContains
  have normalizedSecond : second.segment.Contains normalized := by
    simpa [Cell.sub, periodTranslation, Cell.scale,
      GridSegment.translate, Cell.add] using
      (contains_normalize drawing second.segment
        secondTranslate secondTranslate point).mp secondContains
  have normalizedMember :
      normalized ∈ drawing.fundamentalPoints :=
    fundamental_of_contains
      (endpointBounds second secondMember).1
      (endpointBounds second secondMember).2
      normalizedSecond
  have normalizedFirst :
      (first.segment.translate
        (drawing.periodTranslation relative)).InteriorContains normalized :=
    (interiorContains_normalize drawing first.segment
      firstTranslate secondTranslate point).mp firstContains
  rcases
    finiteRoutesAvoidInteriors_spec checked
      first firstMember second secondMember relative relativeMember
      normalized normalizedMember with same | noFirst | noSecond
  · exact (relative_key_ne different same).elim
  · exact (noFirst normalizedFirst).elim
  · exact (noSecond normalizedSecond).elim

/-- A route occurrence meeting a fundamental-square vertex likewise uses a
neighboring relative translation. -/
theorem relativeTranslate_isNeighbor_of_vertex_contact
    {drawing : PeriodicGridDrawing}
    (endpointBounds : drawing.SegmentEndpointsInFundamentalSquare)
    {vertex : Cell}
    (vertexBounds : drawing.PositionInFundamentalSquare vertex)
    {indexed : IndexedGridSegment}
    (indexedMember : indexed ∈ drawing.indexedSegments)
    {vertexTranslate routeTranslate : Cell}
    (contains :
      (indexed.segment.translate
        (drawing.periodTranslation routeTranslate)).InteriorContains
        (Cell.add vertex
          (drawing.periodTranslation vertexTranslate))) :
    Cell.sub routeTranslate vertexTranslate ∈ neighborTranslations := by
  let relative := Cell.sub routeTranslate vertexTranslate
  have normalized :
      (indexed.segment.translate
        (drawing.periodTranslation relative)).InteriorContains vertex := by
    have := (interiorContains_normalize drawing indexed.segment
      routeTranslate vertexTranslate
      (Cell.add vertex
        (drawing.periodTranslation vertexTranslate))).mp contains
    simpa [relative, normalizePoint, Cell.add, Cell.sub] using this
  have periodPositive : (0 : Int) < drawing.gridSize := by
    exact_mod_cast Nat.zero_lt_succ drawing.gridSizePred
  have segmentBounds := endpointBounds indexed indexedMember
  apply (mem_neighborTranslations_iff relative).mpr
  rcases segmentBounds with ⟨startBounds, finishBounds⟩
  rcases startBounds with
    ⟨startXLower, startXUpper, startYLower, startYUpper⟩
  rcases finishBounds with
    ⟨finishXLower, finishXUpper, finishYLower, finishYUpper⟩
  rcases vertexBounds with
    ⟨pointXLower, pointXUpper, pointYLower, pointYUpper⟩
  rcases normalized with
    ⟨horizontal, same, between⟩ |
      ⟨vertical, same, between⟩
  · have same' :
        vertex.2 =
          indexed.segment.start.2 +
            drawing.gridSize * relative.2 := by
      simpa [GridSegment.translate, periodTranslation,
        Cell.add, Cell.scale, add_comm] using same
    have between' :
        GridSegment.StrictlyBetween
          (indexed.segment.start.1 +
            drawing.gridSize * relative.1)
          (indexed.segment.finish.1 +
            drawing.gridSize * relative.1)
          vertex.1 := by
      simpa [GridSegment.translate, periodTranslation,
        Cell.add, Cell.scale, add_comm] using between
    exact
      ⟨between_shift_is_neighbor periodPositive
          (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) between',
        lane_shift_is_neighbor periodPositive
          (by omega) (by omega) (by omega) (by omega) same'⟩
  · have same' :
        vertex.1 =
          indexed.segment.start.1 +
            drawing.gridSize * relative.1 := by
      simpa [GridSegment.translate, periodTranslation,
        Cell.add, Cell.scale, add_comm] using same
    have between' :
        GridSegment.StrictlyBetween
          (indexed.segment.start.2 +
            drawing.gridSize * relative.2)
          (indexed.segment.finish.2 +
            drawing.gridSize * relative.2)
          vertex.2 := by
      simpa [GridSegment.translate, periodTranslation,
        Cell.add, Cell.scale, add_comm] using between
    exact
      ⟨lane_shift_is_neighbor periodPositive
          (by omega) (by omega) (by omega) (by omega) same',
        between_shift_is_neighbor periodPositive
          (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) between'⟩

/-- The finite neighboring-translation vertex check proves global periodic
vertex/route avoidance. -/
theorem verticesAvoidRouteInteriors_of_finite
    {drawing : PeriodicGridDrawing}
    (endpointBounds : drawing.SegmentEndpointsInFundamentalSquare)
    (vertexBounds :
      ∀ vertex ∈ drawing.vertexPositions,
        drawing.PositionInFundamentalSquare vertex)
    (checked : drawing.finiteVerticesAvoidRouteInteriors = true) :
    drawing.VerticesAvoidRouteInteriors := by
  intro vertex vertexMember indexed indexedMember
    vertexTranslate routeTranslate contains
  let relative := Cell.sub routeTranslate vertexTranslate
  have relativeMember :=
    relativeTranslate_isNeighbor_of_vertex_contact
      endpointBounds (vertexBounds vertex vertexMember)
      indexedMember contains
  have normalized :
      (indexed.segment.translate
        (drawing.periodTranslation relative)).InteriorContains vertex := by
    have := (interiorContains_normalize drawing indexed.segment
      routeTranslate vertexTranslate
      (Cell.add vertex
        (drawing.periodTranslation vertexTranslate))).mp contains
    simpa [relative, normalizePoint, Cell.add, Cell.sub] using this
  exact
    finiteVerticesAvoidRouteInteriors_spec checked
      vertex vertexMember indexed indexedMember relative relativeMember
      normalized

/-- Both finite Boolean checks, together with elementary coordinate bounds,
certify global periodic planarity. -/
theorem isPlanar_of_finite
    {drawing : PeriodicGridDrawing}
    (endpointBounds : drawing.SegmentEndpointsInFundamentalSquare)
    (vertexBounds :
      ∀ vertex ∈ drawing.vertexPositions,
        drawing.PositionInFundamentalSquare vertex)
    (routesChecked : drawing.finiteRoutesAvoidInteriors = true)
    (verticesChecked :
      drawing.finiteVerticesAvoidRouteInteriors = true) :
    drawing.IsPlanar :=
  ⟨routesAvoidInteriors_of_finite endpointBounds routesChecked,
    verticesAvoidRouteInteriors_of_finite
      endpointBounds vertexBounds verticesChecked⟩

end PeriodicGridDrawing
end LeanTrominoes
