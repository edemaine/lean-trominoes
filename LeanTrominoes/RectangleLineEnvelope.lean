import LeanTrominoes.ScaledRectangleLinearNeighborhoodSeparation

/-!
# Closed rectangle-and-line envelopes

The outer radial fan around a retained terminal stays close to two pieces
of data from its discarded source segment: the segment's closed coordinate
rectangle and its supporting line.  The mixed separation certificate says
that every source point or axis-aligned source segment misses at least one
of those two constraints.

This file records the exact complementary contact predicates.  In
particular, it does not reuse `GridSegment.InteriorsMeet`, whose intended
domain is axis-aligned geometry.
-/

namespace LeanTrominoes

/-- A lattice point lies in the closed coordinate rectangle of a reference
segment and on its advertised supporting line. -/
def GridSegment.PointInLinearEnvelope
    (reference : GridSegment) (normal point : Cell) : Prop :=
  InClosedGridRectangle
      reference.coordinateLower reference.coordinateUpper point ∧
    Cell.linearValue normal point =
      Cell.linearValue normal reference.finish

instance (reference : GridSegment) (normal point : Cell) :
    Decidable (reference.PointInLinearEnvelope normal point) := by
  unfold GridSegment.PointInLinearEnvelope
  infer_instance

/-- An axis-aligned source segment has overlapping coordinate rectangles
with a reference segment and brackets the reference supporting line.  These
are precisely the two simultaneous obstructions to the mixed separating-axis
certificate. -/
def GridSegment.AxisSegmentMeetsLinearEnvelope
    (source reference : GridSegment) (normal : Cell) : Prop :=
  source.IsAxisAligned ∧
    ¬ClosedGridRectanglesSeparated
      source.coordinateLower source.coordinateUpper
      reference.coordinateLower reference.coordinateUpper ∧
    GridSegment.Between
      (Cell.linearValue normal source.start)
      (Cell.linearValue normal source.finish)
      (Cell.linearValue normal reference.finish)

instance (source reference : GridSegment) (normal : Cell) :
    Decidable
      (source.AxisSegmentMeetsLinearEnvelope reference normal) := by
  unfold GridSegment.AxisSegmentMeetsLinearEnvelope
  infer_instance

/-- The endpoint used to anchor the supporting line always belongs to its
own closed envelope. -/
theorem GridSegment.finish_pointInLinearEnvelope
    (reference : GridSegment) (normal : Cell) :
    reference.PointInLinearEnvelope normal reference.finish :=
  ⟨reference.finish_in_coordinateRectangle, rfl⟩

/-- The other reference endpoint belongs to the closed envelope whenever
the advertised functional really is constant on the reference segment. -/
theorem GridSegment.start_pointInLinearEnvelope
    (reference : GridSegment) (normal : Cell)
    (sameLine :
      Cell.linearValue normal reference.start =
        Cell.linearValue normal reference.finish) :
    reference.PointInLinearEnvelope normal reference.start :=
  ⟨reference.start_in_coordinateRectangle, sameLine⟩

/-- Pointwise mixed separation is exactly nonmembership in the corresponding
closed rectangle-and-line envelope. -/
theorem pointSeparatesRectangleOrLine_iff_not_pointInLinearEnvelope
    (point : Cell) (reference : GridSegment) (normal : Cell) :
    PointSeparatesRectangleOrLine
        point
        reference.coordinateLower
        reference.coordinateUpper
        reference.finish normal ↔
      ¬reference.PointInLinearEnvelope normal point := by
  rcases reference with
    ⟨⟨startX, startY⟩, ⟨finishX, finishY⟩⟩
  rcases point with ⟨pointX, pointY⟩
  simp only [PointSeparatesRectangleOrLine,
    GridSegment.PointInLinearEnvelope,
    InClosedGridRectangle,
    ClosedGridRectanglesSeparated,
    GridSegment.coordinateLower,
    GridSegment.coordinateUpper,
    Cell.linearValue]
  simp [min_def, max_def]
  omega

/-- For an axis-aligned source segment, mixed separation is exactly the
absence of the rectangle-overlap-and-line-bracketing obstruction. -/
theorem segmentSeparatesRectangleOrLine_iff_not_axisSegmentMeetsLinearEnvelope
    (source reference : GridSegment) (normal : Cell)
    (sourceAligned : source.IsAxisAligned) :
    SegmentSeparatesRectangleOrLine
        source
        reference.coordinateLower
        reference.coordinateUpper
        reference.finish normal ↔
      ¬source.AxisSegmentMeetsLinearEnvelope reference normal := by
  unfold SegmentSeparatesRectangleOrLine
    GridSegment.AxisSegmentMeetsLinearEnvelope
  constructor
  · intro separated contact
    rcases contact with ⟨_, rectanglesMeet, bracketed⟩
    rcases separated with rectanglesSeparated | below | above
    · exact rectanglesMeet rectanglesSeparated
    · simp only [GridSegment.Between] at bracketed
      rcases bracketed with bracketed | bracketed <;> omega
    · simp only [GridSegment.Between] at bracketed
      rcases bracketed with bracketed | bracketed <;> omega
  · intro noContact
    by_cases rectanglesSeparated :
        ClosedGridRectanglesSeparated
          source.coordinateLower source.coordinateUpper
          reference.coordinateLower reference.coordinateUpper
    · exact Or.inl rectanglesSeparated
    · right
      by_contra notLineSeparated
      apply noContact
      refine ⟨sourceAligned, rectanglesSeparated, ?_⟩
      simp only [not_or, not_and, not_lt] at notLineSeparated
      simp only [GridSegment.Between]
      omega

end LeanTrominoes
