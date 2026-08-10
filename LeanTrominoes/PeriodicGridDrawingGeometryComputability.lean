import LeanTrominoes.PeriodicGridDrawingComputability
import LeanTrominoes.PeriodicGridDrawingExpandedFiniteContinuousPlanarity

/-!
# Computability of periodic grid-drawing geometry

This module proves primitive recursiveness of the exact integer and segment
geometry used by the finite periodic drawing certificate.  It includes the
finite enumeration of lattice points in a segment interior.
-/

noncomputable section

namespace LeanTrominoes

namespace Computability

theorem int_min_primrec : Primrec₂ (min : Int → Int → Int) := by
  exact Primrec.ite int_le_primrec Primrec₂.left Primrec₂.right

theorem int_max_primrec : Primrec₂ (max : Int → Int → Int) := by
  exact Primrec.ite int_le_primrec Primrec₂.right Primrec₂.left

/-- The standard finite integer interval enumeration is primitive recursive. -/
theorem int_range_primrec : Primrec₂ Int.range := by
  change Primrec fun input : Int × Int => Int.range input.1 input.2
  unfold Int.range
  have length : Primrec fun input : Int × Int =>
      Int.toNat (input.2 - input.1) :=
    int_toNat_primrec.comp
      (int_subtract_primrec.comp Primrec.snd Primrec.fst)
  exact Primrec.list_map (Primrec.list_range.comp length)
    (int_add_primrec.comp
      (Primrec.fst.comp Primrec.fst)
      (int_ofNat_primrec.comp Primrec.snd)).to₂

end Computability

namespace GridSegment

theorem translate_primrec : Primrec₂ GridSegment.translate := by
  unfold GridSegment.translate
  exact GridSegment.mk_primrec.comp₂
    (Computability.cell_add_primrec.comp₂ Primrec₂.left
      (GridSegment.start_primrec.comp₂ Primrec₂.right))
    (Computability.cell_add_primrec.comp₂ Primrec₂.left
      (GridSegment.finish_primrec.comp₂ Primrec₂.right))

theorem isHorizontal_primrec : PrimrecPred GridSegment.IsHorizontal := by
  unfold GridSegment.IsHorizontal
  exact (Primrec.eq.comp
    (Primrec.snd.comp GridSegment.start_primrec)
    (Primrec.snd.comp GridSegment.finish_primrec)).and
      (Primrec.eq.comp
        (Primrec.fst.comp GridSegment.start_primrec)
        (Primrec.fst.comp GridSegment.finish_primrec)).not

theorem isVertical_primrec : PrimrecPred GridSegment.IsVertical := by
  unfold GridSegment.IsVertical
  exact (Primrec.eq.comp
    (Primrec.fst.comp GridSegment.start_primrec)
    (Primrec.fst.comp GridSegment.finish_primrec)).and
      (Primrec.eq.comp
        (Primrec.snd.comp GridSegment.start_primrec)
        (Primrec.snd.comp GridSegment.finish_primrec)).not

theorem isAxisAligned_primrec :
    PrimrecPred GridSegment.IsAxisAligned := by
  unfold GridSegment.IsAxisAligned
  exact isHorizontal_primrec.or isVertical_primrec

theorem strictlyBetween_primrec : PrimrecPred fun input :
    (Int × Int) × Int =>
    GridSegment.StrictlyBetween input.1.1 input.1.2 input.2 := by
  unfold GridSegment.StrictlyBetween
  exact ((Computability.int_lt_primrec.comp
      (Primrec.fst.comp Primrec.fst) Primrec.snd).and
    (Computability.int_lt_primrec.comp Primrec.snd
      (Primrec.snd.comp Primrec.fst))).or
    ((Computability.int_lt_primrec.comp
      (Primrec.snd.comp Primrec.fst) Primrec.snd).and
    (Computability.int_lt_primrec.comp Primrec.snd
      (Primrec.fst.comp Primrec.fst)))

theorem between_primrec : PrimrecPred fun input :
    (Int × Int) × Int =>
    GridSegment.Between input.1.1 input.1.2 input.2 := by
  unfold GridSegment.Between
  exact ((Computability.int_le_primrec.comp
      (Primrec.fst.comp Primrec.fst) Primrec.snd).and
    (Computability.int_le_primrec.comp Primrec.snd
      (Primrec.snd.comp Primrec.fst))).or
    ((Computability.int_le_primrec.comp
      (Primrec.snd.comp Primrec.fst) Primrec.snd).and
    (Computability.int_le_primrec.comp Primrec.snd
      (Primrec.fst.comp Primrec.fst)))

theorem interiorContains_primrec :
    PrimrecRel GridSegment.InteriorContains := by
  change PrimrecPred fun input : GridSegment × Cell =>
    input.1.InteriorContains input.2
  let horizontal : PrimrecPred fun input : GridSegment × Cell =>
      input.1.IsHorizontal := isHorizontal_primrec.comp Primrec.fst
  let vertical : PrimrecPred fun input : GridSegment × Cell =>
      input.1.IsVertical := isVertical_primrec.comp Primrec.fst
  let sameY : PrimrecPred fun input : GridSegment × Cell =>
      input.2.2 = input.1.start.2 := Primrec.eq.comp
    (Primrec.snd.comp Primrec.snd)
    ((Primrec.snd.comp GridSegment.start_primrec).comp Primrec.fst)
  let sameX : PrimrecPred fun input : GridSegment × Cell =>
      input.2.1 = input.1.start.1 := Primrec.eq.comp
    (Primrec.fst.comp Primrec.snd)
    ((Primrec.fst.comp GridSegment.start_primrec).comp Primrec.fst)
  let betweenX : PrimrecPred fun input : GridSegment × Cell =>
      GridSegment.StrictlyBetween input.1.start.1 input.1.finish.1
        input.2.1 := strictlyBetween_primrec.comp
    (Primrec.pair
      (Primrec.pair
        ((Primrec.fst.comp GridSegment.start_primrec).comp Primrec.fst)
        ((Primrec.fst.comp GridSegment.finish_primrec).comp Primrec.fst))
      (Primrec.fst.comp Primrec.snd))
  let betweenY : PrimrecPred fun input : GridSegment × Cell =>
      GridSegment.StrictlyBetween input.1.start.2 input.1.finish.2
        input.2.2 := strictlyBetween_primrec.comp
    (Primrec.pair
      (Primrec.pair
        ((Primrec.snd.comp GridSegment.start_primrec).comp Primrec.fst)
        ((Primrec.snd.comp GridSegment.finish_primrec).comp Primrec.fst))
      (Primrec.snd.comp Primrec.snd))
  exact (horizontal.and (sameY.and betweenX)).or
    (vertical.and (sameX.and betweenY))

theorem contains_primrec : PrimrecRel GridSegment.Contains := by
  change PrimrecPred fun input : GridSegment × Cell =>
    input.1.Contains input.2
  let horizontal : PrimrecPred fun input : GridSegment × Cell =>
      input.1.IsHorizontal := isHorizontal_primrec.comp Primrec.fst
  let vertical : PrimrecPred fun input : GridSegment × Cell =>
      input.1.IsVertical := isVertical_primrec.comp Primrec.fst
  let sameY : PrimrecPred fun input : GridSegment × Cell =>
      input.2.2 = input.1.start.2 := Primrec.eq.comp
    (Primrec.snd.comp Primrec.snd)
    ((Primrec.snd.comp GridSegment.start_primrec).comp Primrec.fst)
  let sameX : PrimrecPred fun input : GridSegment × Cell =>
      input.2.1 = input.1.start.1 := Primrec.eq.comp
    (Primrec.fst.comp Primrec.snd)
    ((Primrec.fst.comp GridSegment.start_primrec).comp Primrec.fst)
  let betweenX : PrimrecPred fun input : GridSegment × Cell =>
      GridSegment.Between input.1.start.1 input.1.finish.1 input.2.1 :=
    between_primrec.comp
    (Primrec.pair
      (Primrec.pair
        ((Primrec.fst.comp GridSegment.start_primrec).comp Primrec.fst)
        ((Primrec.fst.comp GridSegment.finish_primrec).comp Primrec.fst))
      (Primrec.fst.comp Primrec.snd))
  let betweenY : PrimrecPred fun input : GridSegment × Cell =>
      GridSegment.Between input.1.start.2 input.1.finish.2 input.2.2 :=
    between_primrec.comp
    (Primrec.pair
      (Primrec.pair
        ((Primrec.snd.comp GridSegment.start_primrec).comp Primrec.fst)
        ((Primrec.snd.comp GridSegment.finish_primrec).comp Primrec.fst))
      (Primrec.snd.comp Primrec.snd))
  exact (horizontal.and (sameY.and betweenX)).or
    (vertical.and (sameX.and betweenY))

theorem openIntervalsOverlap_primrec : PrimrecPred fun input :
    (Int × Int) × (Int × Int) =>
    GridSegment.OpenIntervalsOverlap input.1.1 input.1.2
      input.2.1 input.2.2 := by
  unfold GridSegment.OpenIntervalsOverlap
  exact (Computability.int_lt_primrec.comp
    (Computability.int_min_primrec.comp
      (Primrec.fst.comp Primrec.fst)
      (Primrec.snd.comp Primrec.fst))
    (Computability.int_max_primrec.comp
      (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd))).and
    (Computability.int_lt_primrec.comp
      (Computability.int_min_primrec.comp
        (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd))
      (Computability.int_max_primrec.comp
        (Primrec.fst.comp Primrec.fst)
        (Primrec.snd.comp Primrec.fst)))

theorem interiorsMeet_primrec :
    PrimrecRel GridSegment.InteriorsMeet := by
  change PrimrecPred fun input : GridSegment × GridSegment =>
    GridSegment.InteriorsMeet input.1 input.2
  let firstHorizontal : PrimrecPred fun input : GridSegment × GridSegment =>
      input.1.IsHorizontal := isHorizontal_primrec.comp Primrec.fst
  let firstVertical : PrimrecPred fun input : GridSegment × GridSegment =>
      input.1.IsVertical := isVertical_primrec.comp Primrec.fst
  let secondHorizontal : PrimrecPred fun input : GridSegment × GridSegment =>
      input.2.IsHorizontal := isHorizontal_primrec.comp Primrec.snd
  let secondVertical : PrimrecPred fun input : GridSegment × GridSegment =>
      input.2.IsVertical := isVertical_primrec.comp Primrec.snd
  let firstStartX : Primrec fun input : GridSegment × GridSegment =>
      input.1.start.1 :=
    (Primrec.fst.comp GridSegment.start_primrec).comp Primrec.fst
  let firstStartY : Primrec fun input : GridSegment × GridSegment =>
      input.1.start.2 :=
    (Primrec.snd.comp GridSegment.start_primrec).comp Primrec.fst
  let firstFinishX : Primrec fun input : GridSegment × GridSegment =>
      input.1.finish.1 :=
    (Primrec.fst.comp GridSegment.finish_primrec).comp Primrec.fst
  let firstFinishY : Primrec fun input : GridSegment × GridSegment =>
      input.1.finish.2 :=
    (Primrec.snd.comp GridSegment.finish_primrec).comp Primrec.fst
  let secondStartX : Primrec fun input : GridSegment × GridSegment =>
      input.2.start.1 :=
    (Primrec.fst.comp GridSegment.start_primrec).comp Primrec.snd
  let secondStartY : Primrec fun input : GridSegment × GridSegment =>
      input.2.start.2 :=
    (Primrec.snd.comp GridSegment.start_primrec).comp Primrec.snd
  let secondFinishX : Primrec fun input : GridSegment × GridSegment =>
      input.2.finish.1 :=
    (Primrec.fst.comp GridSegment.finish_primrec).comp Primrec.snd
  let secondFinishY : Primrec fun input : GridSegment × GridSegment =>
      input.2.finish.2 :=
    (Primrec.snd.comp GridSegment.finish_primrec).comp Primrec.snd
  let overlapX := openIntervalsOverlap_primrec.comp
    (Primrec.pair
      (Primrec.pair firstStartX firstFinishX)
      (Primrec.pair secondStartX secondFinishX))
  let overlapY := openIntervalsOverlap_primrec.comp
    (Primrec.pair
      (Primrec.pair firstStartY firstFinishY)
      (Primrec.pair secondStartY secondFinishY))
  let secondXBetweenFirst := strictlyBetween_primrec.comp
    (Primrec.pair (Primrec.pair firstStartX firstFinishX) secondStartX)
  let firstYBetweenSecond := strictlyBetween_primrec.comp
    (Primrec.pair (Primrec.pair secondStartY secondFinishY) firstStartY)
  let firstXBetweenSecond := strictlyBetween_primrec.comp
    (Primrec.pair (Primrec.pair secondStartX secondFinishX) firstStartX)
  let secondYBetweenFirst := strictlyBetween_primrec.comp
    (Primrec.pair (Primrec.pair firstStartY firstFinishY) secondStartY)
  exact (firstHorizontal.and (secondHorizontal.and
      ((Primrec.eq.comp firstStartY secondStartY).and overlapX))).or
    ((firstVertical.and (secondVertical.and
      ((Primrec.eq.comp firstStartX secondStartX).and overlapY))).or
    ((firstHorizontal.and (secondVertical.and
      (secondXBetweenFirst.and firstYBetweenSecond))).or
    (firstVertical.and (secondHorizontal.and
      (firstXBetweenSecond.and secondYBetweenFirst)))))

end GridSegment

namespace PeriodicGridDrawing

/-- Enumerating the integer coordinates strictly between two endpoints is
primitive recursive. -/
theorem strictlyBetweenCoordinates_primrec :
    Primrec₂ strictlyBetweenCoordinates := by
  change Primrec fun input : Int × Int =>
    strictlyBetweenCoordinates input.1 input.2
  unfold strictlyBetweenCoordinates
  exact Primrec.list_append.comp₂
    (Computability.int_range_primrec.comp₂
      (Computability.int_add_primrec.comp₂ Primrec₂.left
        (Primrec₂.const (1 : Int)))
      Primrec₂.right)
    (Computability.int_range_primrec.comp₂
      (Computability.int_add_primrec.comp₂ Primrec₂.right
        (Primrec₂.const (1 : Int)))
      Primrec₂.left)

/-- Enumerating all lattice points in a segment interior is primitive
recursive. -/
theorem segmentInteriorPoints_primrec :
    Primrec (segmentInteriorPoints : GridSegment → List Cell) := by
  let horizontalCoordinates : Primrec fun segment : GridSegment =>
      strictlyBetweenCoordinates segment.start.1 segment.finish.1 :=
    strictlyBetweenCoordinates_primrec.comp
      (Primrec.fst.comp GridSegment.start_primrec)
      (Primrec.fst.comp GridSegment.finish_primrec)
  let horizontalPoints : Primrec fun segment : GridSegment =>
      (strictlyBetweenCoordinates segment.start.1 segment.finish.1).map
        fun horizontal => (horizontal, segment.start.2) :=
    Primrec.list_map horizontalCoordinates
      (Primrec.pair Primrec.snd
        ((Primrec.snd.comp GridSegment.start_primrec).comp
          Primrec.fst)).to₂
  let horizontal : Primrec fun segment : GridSegment =>
      if segment.IsHorizontal then
        (strictlyBetweenCoordinates segment.start.1 segment.finish.1).map
          fun horizontal => (horizontal, segment.start.2)
      else [] :=
    Primrec.ite GridSegment.isHorizontal_primrec horizontalPoints
      (Primrec.const [])
  let verticalCoordinates : Primrec fun segment : GridSegment =>
      strictlyBetweenCoordinates segment.start.2 segment.finish.2 :=
    strictlyBetweenCoordinates_primrec.comp
      (Primrec.snd.comp GridSegment.start_primrec)
      (Primrec.snd.comp GridSegment.finish_primrec)
  let verticalPoints : Primrec fun segment : GridSegment =>
      (strictlyBetweenCoordinates segment.start.2 segment.finish.2).map
        fun vertical => (segment.start.1, vertical) :=
    Primrec.list_map verticalCoordinates
      (Primrec.pair
        ((Primrec.fst.comp GridSegment.start_primrec).comp Primrec.fst)
        Primrec.snd).to₂
  let vertical : Primrec fun segment : GridSegment =>
      if segment.IsVertical then
        (strictlyBetweenCoordinates segment.start.2 segment.finish.2).map
          fun vertical => (segment.start.1, vertical)
      else [] :=
    Primrec.ite GridSegment.isVertical_primrec verticalPoints
      (Primrec.const [])
  exact (Primrec.list_append.comp horizontal vertical).of_eq fun _ => rfl

theorem segmentOccurrenceKey_primrec :
    Primrec₂ PeriodicGridDrawing.SegmentOccurrenceKey := by
  unfold PeriodicGridDrawing.SegmentOccurrenceKey
  exact Primrec₂.pair.comp₂
    (IndexedGridSegment.routeIndex_primrec.comp₂ Primrec₂.left)
    (Primrec₂.pair.comp₂
      (IndexedGridSegment.segmentIndex_primrec.comp₂ Primrec₂.left)
      Primrec₂.right)

theorem routePointOccurrenceKey_primrec :
    Primrec₂ PeriodicGridDrawing.RoutePointOccurrenceKey := by
  unfold PeriodicGridDrawing.RoutePointOccurrenceKey
  exact Primrec₂.pair.comp₂
    (IndexedRoutePoint.routeIndex_primrec.comp₂ Primrec₂.left)
    (Primrec₂.pair.comp₂
      (IndexedRoutePoint.pointIndex_primrec.comp₂ Primrec₂.left)
      Primrec₂.right)

end PeriodicGridDrawing

namespace IndexedRoutePoint

theorem isEndpoint_primrec :
    PrimrecPred IndexedRoutePoint.IsEndpoint := by
  unfold IndexedRoutePoint.IsEndpoint
  exact (Primrec.eq.comp pointIndex_primrec (Primrec.const 0)).or
    (Primrec.eq.comp
      (Primrec.nat_add.comp pointIndex_primrec (Primrec.const 1))
      routeLength_primrec)

end IndexedRoutePoint

end LeanTrominoes
