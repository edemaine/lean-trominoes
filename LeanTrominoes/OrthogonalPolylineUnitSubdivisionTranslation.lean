import LeanTrominoes.OrthogonalPolylineLoopErasure

/-!
# Translation of unit-subdivided orthogonal polylines

Unit subdivision is equivariant under an integral translation.  Consequently
endpoint-isolation certificates proved for a finite local route transport to
every positioned copy of that route.
-/

namespace LeanTrominoes
namespace AxisDirection

/-- Translation preserves the Manhattan length used to enumerate a unit
segment. -/
@[simp]
theorem segmentLength_add_left
    (offset first second : Cell) :
    segmentLength (Cell.add offset first)
        (Cell.add offset second) =
      segmentLength first second := by
  rcases offset with ⟨offsetX, offsetY⟩
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  simp [segmentLength, Cell.add]

/-- Translating a segment translates its ordered list of unit points. -/
theorem unitSegmentPoints_add_left
    (offset first second : Cell) :
    unitSegmentPoints (Cell.add offset first)
        (Cell.add offset second) =
      (unitSegmentPoints first second).map (Cell.add offset) := by
  simp only [unitSegmentPoints, segmentLength_add_left,
    between_add_left, List.map_map]
  apply List.map_congr_left
  intro index _indexMember
  rcases offset with ⟨offsetX, offsetY⟩
  rcases first with ⟨firstX, firstY⟩
  rcases stepEquation :
      (between (firstX, firstY) second).step with
    ⟨stepX, stepY⟩
  simp [Cell.add, Cell.scale]
  constructor <;> ring

/-- Translating a polyline commutes with ordered unit subdivision. -/
theorem unitSubdividePolyline_map_add
    (offset : Cell) (points : List Cell) :
    unitSubdividePolyline (points.map (Cell.add offset)) =
      (unitSubdividePolyline points).map (Cell.add offset) := by
  induction points using List.twoStepInduction with
  | nil | singleton => simp
  | cons_cons first second rest _ tailInduction =>
      rw [List.map_cons, List.map_cons,
        unitSubdividePolyline, unitSubdividePolyline,
        unitSegmentPoints_add_left]
      change
        LeanTrominoes.joinAtEndpoint
            ((unitSegmentPoints first second).map
              (Cell.add offset))
            (unitSubdividePolyline
              ((second :: rest).map (Cell.add offset))) =
          (LeanTrominoes.joinAtEndpoint
            (unitSegmentPoints first second)
            (unitSubdividePolyline (second :: rest))).map
              (Cell.add offset)
      rw [tailInduction second]
      simp [LeanTrominoes.joinAtEndpoint, List.map_append]

/-- Translation preserves isolation of the first point after unit
subdivision. -/
theorem HeadNotInTail.unitSubdividePolyline_map_add
    {points : List Cell}
    (fresh : HeadNotInTail (unitSubdividePolyline points))
    (offset : Cell) :
    HeadNotInTail
      (unitSubdividePolyline (points.map (Cell.add offset))) := by
  rw [LeanTrominoes.AxisDirection.unitSubdividePolyline_map_add
    offset points]
  exact fresh.map_of_injective
    (Cell.add_left_injective offset)

/-- Translation preserves isolation of the final point after unit
subdivision. -/
theorem LastNotInDropLast.unitSubdividePolyline_map_add
    {points : List Cell}
    (fresh : LastNotInDropLast (unitSubdividePolyline points))
    (offset : Cell) :
    LastNotInDropLast
      (unitSubdividePolyline (points.map (Cell.add offset))) := by
  rw [LeanTrominoes.AxisDirection.unitSubdividePolyline_map_add
    offset points]
  exact fresh.map_of_injective
    (Cell.add_left_injective offset)

end AxisDirection
end LeanTrominoes
