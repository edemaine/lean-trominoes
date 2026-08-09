import LeanTrominoes.OrthogonalPolylineScaling
import LeanTrominoes.OrthogonalPolylineUnitSubdivisionJoin
import LeanTrominoes.PeriodicThreeDMNormalizationRouteRasterization

/-!
# Validity of degree-three normalization routes

The rasterizer expects every normalized edge route to consist of unit axis
steps without immediate reversals.  This module establishes those invariants
from the continuous planar presentation.  The first layer below isolates the
generic affine magnification, unit subdivision, and endpoint trimming shared
by all three normalization rounds.
-/

namespace LeanTrominoes

open Gadget
open DegreeThreeVertexNormalization

namespace PeriodicThreeDM

/-- Mapping the normalization affine map is scaling followed by translation
by the template center. -/
theorem map_normalizeVertexPosition_eq_translate_scalePolyline
    (points : List Cell) :
    points.map normalizeVertexPosition =
      PeriodicOrthocrossing.translatePolyline center
        (scalePolyline vertexNormalizationScale points) := by
  induction points with
  | nil => rfl
  | cons point rest induction =>
      simp only [List.map_cons, scalePolyline_cons,
        PeriodicOrthocrossing.translatePolyline, induction]
      rw [show normalizeVertexPosition point =
          Cell.add center (Cell.scale vertexNormalizationScale point) by
        simp [normalizeVertexPosition, Cell.add_comm]]

/-- Affine magnification and ordered unit subdivision preserve
orthogonality. -/
theorem magnifiedUnitRoute_orthogonal
    {points : List Cell}
    (orthogonal : PeriodicOrthocrossing.OrthogonalPolyline points) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (magnifiedUnitRoute points) := by
  unfold magnifiedUnitRoute
  rw [map_normalizeVertexPosition_eq_translate_scalePolyline]
  apply AxisDirection.unitSubdividePolyline_orthogonal
  have scaled : PeriodicOrthocrossing.OrthogonalPolyline
      (scalePolyline vertexNormalizationScale points) := by
    simpa [vertexNormalizationScale] using
      PeriodicOrthocrossing.OrthogonalPolyline.scalePolyline
        orthogonal (factor := 12) (by norm_num)
  exact scaled.translate center

/-- Every magnified and subdivided orthogonal route consists of unit axis
steps. -/
theorem magnifiedUnitRoute_unitSteps
    {points : List Cell}
    (orthogonal : PeriodicOrthocrossing.OrthogonalPolyline points) :
    (magnifiedUnitRoute points).IsChain
      AxisDirection.IsUnitAxisStep := by
  unfold magnifiedUnitRoute
  rw [map_normalizeVertexPosition_eq_translate_scalePolyline]
  apply AxisDirection.unitSubdividePolyline_unitSteps
  have scaled : PeriodicOrthocrossing.OrthogonalPolyline
      (scalePolyline vertexNormalizationScale points) := by
    simpa [vertexNormalizationScale] using
      PeriodicOrthocrossing.OrthogonalPolyline.scalePolyline
        orthogonal (factor := 12) (by norm_num)
  exact scaled.translate center

/-- Dropping and taking the endpoint clearance margins preserves the
unit-step chain. -/
theorem trimmedMagnifiedRoute_unitSteps
    {points : List Cell}
    (orthogonal : PeriodicOrthocrossing.OrthogonalPolyline points) :
    (trimmedMagnifiedRoute points).IsChain
      AxisDirection.IsUnitAxisStep := by
  unfold trimmedMagnifiedRoute
  exact ((magnifiedUnitRoute_unitSteps orthogonal).drop 3).take _

/-- The trimmed middle is consequently still an orthogonal polyline. -/
theorem trimmedMagnifiedRoute_orthogonal
    {points : List Cell}
    (orthogonal : PeriodicOrthocrossing.OrthogonalPolyline points) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (trimmedMagnifiedRoute points) := by
  exact (trimmedMagnifiedRoute_unitSteps orthogonal).imp
    fun _ _ step => step.isAxisAligned

/-- Dropping three entries from a sufficiently long subdivided segment
lands exactly three unit steps from its initial endpoint. -/
theorem unitSegmentPoints_drop_three_head?
    {first second : Cell}
    (long : 3 < AxisDirection.segmentLength first second + 1) :
    ((AxisDirection.unitSegmentPoints first second).drop 3).head? =
      some (Cell.add first
        (Cell.scale 3 (AxisDirection.between first second).step)) := by
  simp [AxisDirection.unitSegmentPoints, List.head?_eq_getElem?, long]

/-- Taking a positive number of entries preserves a list's optional head. -/
theorem List.head?_take_of_pos
    {α : Type*} (items : List α) {count : Nat}
    (positive : 0 < count) :
    (items.take count).head? = items.head? := by
  cases items <;> cases count <;> simp_all

/-- Dropping strictly within a left summand makes the right summand
irrelevant to the resulting head. -/
theorem List.head?_drop_append_of_lt_length
    {α : Type*} (first second : List α) {count : Nat}
    (within : count < first.length) :
    ((first ++ second).drop count).head? =
      (first.drop count).head? := by
  rw [List.drop_append_of_le_length (Nat.le_of_lt within)]
  have nonempty : first.drop count ≠ [] := by
    intro empty
    have : (first.drop count).length = 0 := by simp [empty]
    simp only [List.length_drop] at this
    omega
  exact List.head?_append_of_ne_nil _ nonempty

/-- Positive affine normalization preserves the direction between two
points. -/
@[simp]
theorem between_normalizeVertexPosition (first second : Cell) :
    AxisDirection.between
        (normalizeVertexPosition first) (normalizeVertexPosition second) =
      AxisDirection.between first second := by
  have scaled := AxisDirection.polylineFirstDirection_scalePolyline
    vertexNormalizationScale (by norm_num [vertexNormalizationScale])
    [first, second]
  simpa [normalizeVertexPosition, Cell.add_comm,
    AxisDirection.polylineFirstDirection,
    PeriodicOrthocrossing.translatePolyline,
    AxisDirection.between_add_left] using scaled

/-- The trimmed magnified route starts exactly three unit steps along the
original route's first directed segment. -/
theorem trimmedMagnifiedRoute_head?_of_cons_cons
    (first second : Cell) (rest : List Cell)
    (aligned : (GridSegment.mk first second).IsAxisAligned) :
    (trimmedMagnifiedRoute (first :: second :: rest)).head? =
      some (Cell.add (normalizeVertexPosition first)
        (Cell.scale 3 (AxisDirection.between first second).step)) := by
  have magnifiedLength :=
    magnifiedUnitRoute_cons_cons_length_ge_thirteen
      first second rest aligned
  have takePositive :
      0 < (magnifiedUnitRoute (first :: second :: rest)).length - 6 := by
    omega
  unfold trimmedMagnifiedRoute
  rw [List.head?_take_of_pos _ takePositive]
  unfold magnifiedUnitRoute
  simp only [List.map_cons]
  rw [AxisDirection.unitSubdividePolyline]
  unfold LeanTrominoes.joinAtEndpoint
  have normalizedLong :
      3 < AxisDirection.segmentLength
          (normalizeVertexPosition first)
          (normalizeVertexPosition second) + 1 := by
    rw [segmentLength_normalizeVertexPosition]
    have positive := AxisDirection.segmentLength_positive_of_axisAligned aligned
    omega
  rw [List.head?_drop_append_of_lt_length _ _ (by
    simpa using normalizedLong)]
  rw [unitSegmentPoints_drop_three_head? normalizedLong]
  simp

/-- Trimming three points at each end leaves the original point three
steps before the last as its new final point. -/
theorem List.getLast?_drop_three_take_length_sub_six
    {α : Type*} (items : List α)
    (long : 7 ≤ items.length) :
    ((items.drop 3).take (items.length - 6)).getLast? =
      items[items.length - 4]? := by
  rw [List.getLast?_eq_getElem?]
  simp only [List.length_take, List.length_drop]
  rw [Nat.min_eq_left (by omega)]
  simp only [List.getElem?_take, List.getElem?_drop]
  rw [if_pos (by omega)]
  rw [show 3 + (items.length - 6 - 1) = items.length - 4 by omega]

/-- On a long axis-aligned segment, the point three entries before the
last endpoint is three reverse unit steps from that endpoint. -/
theorem unitSegmentPoints_getElem?_three_before_last
    {first second : Cell}
    (aligned : (GridSegment.mk first second).IsAxisAligned)
    (long : 3 ≤ AxisDirection.segmentLength first second) :
    (AxisDirection.unitSegmentPoints first second)[
        AxisDirection.segmentLength first second - 3]? =
      some (Cell.add second
        (Cell.scale 3 (AxisDirection.between second first).step)) := by
  rw [List.getElem?_eq_getElem (by
    simp [AxisDirection.unitSegmentPoints])]
  simp only [AxisDirection.unitSegmentPoints, List.getElem_map,
    List.getElem_range]
  have endpoint :=
    AxisDirection.add_length_step_eq_second_of_axisAligned aligned
  have genuine := AxisDirection.between_isGenuine_of_axisAligned aligned
  have reverse := AxisDirection.between_reverse_eq_opposite genuine
  rw [reverse]
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  cases direction : AxisDirection.between
      (firstX, firstY) (secondX, secondY) <;>
    simp_all only [AxisDirection.IsGenuine, AxisDirection.opposite,
      AxisDirection.step, Cell.add, Cell.scale, Prod.mk.injEq,
      Option.some.injEq] <;>
    omega

/-- Unit subdivision of a polyline displayed with a final pair is an
endpoint join with the subdivision of that final segment. -/
theorem unitSubdividePolyline_append_pair
    (leading : List Cell) (before last : Cell) :
    AxisDirection.unitSubdividePolyline
        (leading ++ [before, last]) =
      joinAtEndpoint
        (AxisDirection.unitSubdividePolyline
          (leading ++ [before]))
        (AxisDirection.unitSegmentPoints before last) := by
  have joined :
      joinAtEndpoint (leading ++ [before]) [before, last] =
        leading ++ [before, last] := by
    simp [joinAtEndpoint]
  rw [← joined]
  rw [AxisDirection.unitSubdividePolyline_joinAtEndpoint
    (middle := before) (by simp) (by simp) (by simp)]
  simp [AxisDirection.unitSubdividePolyline, joinAtEndpoint]

/-- The trimmed magnified route ends exactly three reverse unit steps along
the original route's final directed segment. -/
theorem trimmedMagnifiedRoute_getLast?_of_append_pair
    (leading : List Cell) (before last : Cell)
    (aligned : (GridSegment.mk before last).IsAxisAligned) :
    (trimmedMagnifiedRoute (leading ++ [before, last])).getLast? =
      some (Cell.add (normalizeVertexPosition last)
        (Cell.scale 3 (AxisDirection.between last before).step)) := by
  let initialRoute := AxisDirection.unitSubdividePolyline
    ((leading ++ [before]).map normalizeVertexPosition)
  let finalSegment := AxisDirection.unitSegmentPoints
    (normalizeVertexPosition before) (normalizeVertexPosition last)
  have magnifiedEquation :
      magnifiedUnitRoute (leading ++ [before, last]) =
        joinAtEndpoint initialRoute finalSegment := by
    unfold magnifiedUnitRoute
    simp only [List.map_append, List.map_cons, List.map_nil]
    rw [unitSubdividePolyline_append_pair]
    simp [initialRoute, finalSegment]
  have oldPositive :=
    AxisDirection.segmentLength_positive_of_axisAligned aligned
  have normalizedVeryLong :
      12 ≤ AxisDirection.segmentLength
        (normalizeVertexPosition before) (normalizeVertexPosition last) := by
    rw [segmentLength_normalizeVertexPosition]
    omega
  have normalizedLong :
      3 ≤ AxisDirection.segmentLength
        (normalizeVertexPosition before) (normalizeVertexPosition last) :=
    le_trans (by omega) normalizedVeryLong
  have segmentLength : 13 ≤ finalSegment.length := by
    simp only [finalSegment, AxisDirection.unitSegmentPoints_length,
      segmentLength_normalizeVertexPosition]
    omega
  have initialRouteNonempty : initialRoute ≠ [] := by
    apply AxisDirection.unitSubdividePolyline_ne_nil
    simp
  have initialRoutePositive : 0 < initialRoute.length :=
    List.length_pos_of_ne_nil initialRouteNonempty
  have magnifiedLong :
      13 ≤ (magnifiedUnitRoute (leading ++ [before, last])).length := by
    rw [magnifiedEquation]
    simp only [joinAtEndpoint, List.length_append, List.length_tail]
    omega
  unfold trimmedMagnifiedRoute
  rw [List.getLast?_drop_three_take_length_sub_six _
    (le_trans (by omega) magnifiedLong)]
  rw [magnifiedEquation]
  unfold joinAtEndpoint
  rw [List.getElem?_append_right (by
    simp only [List.length_append, List.length_tail]
    omega)]
  simp only [List.length_append, List.length_tail]
  rw [show
    initialRoute.length + (finalSegment.length - 1) - 4 -
        initialRoute.length =
      finalSegment.length - 1 - 4 by omega]
  rw [List.getElem?_tail]
  have normalizedAligned :
      (GridSegment.mk
        (normalizeVertexPosition before)
        (normalizeVertexPosition last)).IsAxisAligned := by
    have scaledAligned :
        (GridSegment.scale vertexNormalizationScale
          (GridSegment.mk before last)).IsAxisAligned :=
      (GridSegment.isAxisAligned_scale_iff
        (by norm_num [vertexNormalizationScale])
        (GridSegment.mk before last)).2 aligned
    have translatedAligned :=
      (GridSegment.isAxisAligned_translate
        (GridSegment.scale vertexNormalizationScale
          (GridSegment.mk before last)) center).2 scaledAligned
    simpa [GridSegment.scale, GridSegment.translate,
      normalizeVertexPosition, Cell.add_comm] using translatedAligned
  have normalizedIndex :
      AxisDirection.segmentLength
          (normalizeVertexPosition before) (normalizeVertexPosition last) - 4 + 1 =
        AxisDirection.segmentLength
          (normalizeVertexPosition before) (normalizeVertexPosition last) - 3 := by
    omega
  simpa only [finalSegment, AxisDirection.unitSegmentPoints_length,
    Nat.add_sub_cancel,
    Nat.sub_add_comm (by omega : 1 ≤ finalSegment.length),
    normalizedIndex, between_normalizeVertexPosition] using
    unitSegmentPoints_getElem?_three_before_last
      normalizedAligned normalizedLong

end PeriodicThreeDM
end LeanTrominoes
