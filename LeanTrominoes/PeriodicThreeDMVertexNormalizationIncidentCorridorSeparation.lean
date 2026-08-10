import LeanTrominoes.PeriodicThreeDMVertexNormalizationCorridorSeparation
import LeanTrominoes.OrthogonalPolylineLinearSeparation
import Mathlib.Data.List.DropRight

/-!
# Separation of incident normalization corridors

At an endpoint of an old route, its trimmed magnified corridor begins three
unit steps from the new vertex center and continues outward through the old
endpoint direction.  This module proves that the corridor strictly avoids
every other Figure 2 arm at that center.  The initial radial part is separated
by a directional linear bound; after the next old route point, simplicity and
the scale-twelve neighborhood theorem supply the required clearance.
-/

namespace LeanTrominoes

open PeriodicEightOccurrenceSplit
open PeriodicOrthocrossing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
open DegreeThreeVertexNormalization

namespace PeriodicThreeDM

/-- Every Figure 2 arm other than the one assigned to a used side stays on
the center side of the hyperplane perpendicular to that side. -/
theorem route_linearValue_le_center_of_port_ne_side
    (omitted side : VertexSide) (port : CanonicalVertexPort)
    (used : side ≠ omitted)
    (different : port ≠ canonicalPortForSide omitted side) :
    ∀ point ∈ route omitted port,
      Cell.linearValue side.direction.step point ≤
        Cell.linearValue side.direction.step center + 2 := by
  cases omitted <;> cases side <;> cases port <;>
    simp_all [route, canonicalPortForSide, VertexSide.direction,
      AxisDirection.step, Cell.linearValue, center]

/-- The same directional half-plane bound after anchoring the local
template at an arbitrary old lattice position. -/
theorem normalizationTemplateAt_route_linearValue_le_center_of_port_ne_side
    (position : Cell) (omitted side : VertexSide)
    (port : CanonicalVertexPort)
    (used : side ≠ omitted)
    (different : port ≠ canonicalPortForSide omitted side) :
    ∀ point ∈ normalizationTemplateAt position (route omitted port),
      Cell.linearValue side.direction.step point ≤
        Cell.linearValue side.direction.step
          (normalizeVertexPosition position) + 2 := by
  intro point pointMember
  unfold normalizationTemplateAt
    PeriodicOrthocrossing.translatePolyline at pointMember
  rcases List.mem_map.mp pointMember with
    ⟨localPoint, localMember, rfl⟩
  have localBound :=
    route_linearValue_le_center_of_port_ne_side
      omitted side port used different localPoint localMember
  simp only [normalizeVertexPosition, Cell.linearValue_add]
  omega

/-- Dropping commutes with pointwise mapping. -/
theorem List.drop_map_eq
    {α β : Type*} (count : Nat) (function : α → β)
    (items : List α) :
    (items.map function).drop count =
      (items.drop count).map function := by
  induction count generalizing items with
  | zero => simp
  | succ count induction =>
      cases items with
      | nil => simp
      | cons item rest =>
          change (rest.map function).drop count =
            (rest.drop count).map function
          exact induction rest

/-- Dropping the first three entries of an ordered unit subdivision leaves
only points strictly beyond its starting hyperplane. -/
theorem unitSegmentPoints_drop_three_linearValue_gt
    {first second : Cell} (side : VertexSide)
    (direction : AxisDirection.between first second = side.direction) :
    ∀ point ∈ (AxisDirection.unitSegmentPoints first second).drop 3,
      Cell.linearValue side.direction.step first + 2 <
        Cell.linearValue side.direction.step point := by
  intro point pointMember
  unfold AxisDirection.unitSegmentPoints at pointMember
  rw [List.drop_map_eq] at pointMember
  rcases List.mem_map.mp pointMember with
    ⟨index, indexMember, rfl⟩
  have indexLower : 3 ≤ index := by
    rcases List.mem_iff_get.mp indexMember with ⟨listIndex, indexAt⟩
    simp at indexAt
    omega
  rw [direction]
  rcases first with ⟨firstX, firstY⟩
  cases side <;>
    simp [VertexSide.direction, AxisDirection.step,
      Cell.add, Cell.scale, Cell.linearValue] <;>
    omega

/-- The symmetric three-entry trim commutes with reversal. -/
theorem List.drop_take_eq_take_drop
    {α : Type*} (items : List α) (dropCount takeCount : Nat) :
    (items.take takeCount).drop dropCount =
      (items.drop dropCount).take (takeCount - dropCount) := by
  induction dropCount generalizing items takeCount with
  | zero => simp
  | succ dropCount induction =>
      cases items with
      | nil => simp
      | cons item rest =>
          cases takeCount with
          | zero => simp
          | succ takeCount =>
              simpa using induction rest takeCount

theorem List.symmetricTrim_eq_drop_rdrop
    {α : Type*} (items : List α) :
    (items.drop 3).take (items.length - 6) =
      (items.drop 3).rdrop 3 := by
  unfold List.rdrop
  congr 1
  simp only [List.length_drop]
  omega

theorem List.drop_rdrop_comm
    {α : Type*} (items : List α) (count : Nat) :
    (items.rdrop count).drop count =
      (items.drop count).rdrop count := by
  unfold List.rdrop
  rw [List.drop_take_eq_take_drop]
  congr 1
  simp only [List.length_drop]

theorem List.symmetricTrim_reverse
    {α : Type*} (items : List α) :
    ((items.reverse.drop 3).take (items.length - 6)) =
      ((items.drop 3).take (items.length - 6)).reverse := by
  have reversed := List.symmetricTrim_eq_drop_rdrop items.reverse
  simp only [List.length_reverse] at reversed
  rw [reversed, List.symmetricTrim_eq_drop_rdrop]
  rw [List.rdrop_eq_reverse_drop_reverse]
  rw [show (items.reverse.drop 3).reverse = items.rdrop 3 by
    exact (List.rdrop_eq_reverse_drop_reverse items 3).symm]
  rw [List.drop_rdrop_comm]

/-- Reversing an endpoint join swaps its two pieces. -/
theorem joinAtEndpoint_reverse
    {α : Type*} {first second : List α} {boundary : α}
    (firstLast : first.getLast? = some boundary)
    (secondHead : second.head? = some boundary) :
    (joinAtEndpoint first second).reverse =
      joinAtEndpoint second.reverse first.reverse := by
  have boundaryMember : boundary ∈ first.getLast? := by
    simp [firstLast]
  have firstEquation :=
    List.dropLast_append_getLast? boundary boundaryMember
  cases second with
  | nil => simp at secondHead
  | cons actualBoundary rest =>
      have boundaryEqual : actualBoundary = boundary :=
        Option.some.inj secondHead
      subst actualBoundary
      rw [← firstEquation]
      simp [joinAtEndpoint, List.reverse_append]

/-- Reversing a trimmed ordered segment leaves points at least three steps
beyond its former final endpoint in the reverse direction. -/
theorem unitSegmentPoints_reverse_drop_three_linearValue_gt
    {first second : Cell} (side : VertexSide)
    (aligned : (GridSegment.mk first second).IsAxisAligned)
    (direction : AxisDirection.between second first = side.direction) :
    ∀ point ∈
        (AxisDirection.unitSegmentPoints first second).reverse.drop 3,
      Cell.linearValue side.direction.step second + 2 <
        Cell.linearValue side.direction.step point := by
  intro point pointMember
  unfold AxisDirection.unitSegmentPoints at pointMember
  rw [← List.map_reverse, List.drop_map_eq] at pointMember
  rcases List.mem_map.mp pointMember with
    ⟨index, indexMember, rfl⟩
  have indexUpper :
      index + 3 ≤ AxisDirection.segmentLength first second := by
    rcases List.mem_iff_get.mp indexMember with
      ⟨listIndex, indexAt⟩
    have listIndexBound :
        listIndex.val <
          AxisDirection.segmentLength first second + 1 - 3 := by
      simpa using listIndex.isLt
    simp at indexAt
    omega
  have genuine :=
    AxisDirection.between_isGenuine_of_axisAligned aligned
  have reverseDirection :=
    AxisDirection.between_reverse_eq_opposite genuine
  have originalDirection :
      AxisDirection.between first second = side.direction.opposite := by
    rw [direction] at reverseDirection
    cases side <;>
      cases actual : AxisDirection.between first second <;>
      simp_all [VertexSide.direction, AxisDirection.opposite,
        AxisDirection.IsGenuine]
  have endpoint :=
    AxisDirection.add_length_step_eq_second_of_axisAligned aligned
  rw [originalDirection]
  rw [originalDirection] at endpoint
  rw [← endpoint]
  rcases first with ⟨firstX, firstY⟩
  cases side <;>
    simp [VertexSide.direction, AxisDirection.opposite,
      AxisDirection.step, Cell.add, Cell.scale, Cell.linearValue] <;>
    omega

/-- The last point of a nonempty dropped suffix is still the last point of
the original list. -/
theorem List.getLast?_drop_eq_getLast?_of_lt
    {items : List Cell} {count : Nat}
    (within : count < items.length) :
    (items.drop count).getLast? = items.getLast? := by
  induction count generalizing items with
  | zero => simp
  | succ count induction =>
      cases items with
      | nil => simp at within
      | cons first rest =>
          have restNonempty : rest ≠ [] := by
            intro restEmpty
            subst rest
            simp at within
          simp only [List.drop_succ_cons]
          rw [induction (by simpa using within)]
          cases rest with
          | nil => exact (restNonempty rfl).elim
          | cons second trailing => simp

/-- A simple route with its last point removed avoids that old endpoint at
both listed points and along every surviving segment. -/
theorem LocalIncidenceDrawing.RouteIsSimple.dropLast_avoids_last
    {route : List Cell} {last : Cell}
    (simple : LocalIncidenceDrawing.RouteIsSimple route)
    (lastLookup : route.getLast? = some last) :
    (∀ point ∈ route.dropLast, point ≠ last) ∧
      ∀ segment ∈ gridPolylineSegments route.dropLast,
        segment.IsAxisAligned → ¬segment.Contains last := by
  have lastMember : last ∈ route := by
    exact List.mem_of_mem_getLast? lastLookup
  have lastFresh : last ∉ route.dropLast :=
    AxisDirection.lastNotInDropLast_of_nodup
      simple.1 last lastLookup
  constructor
  · intro point pointMember pointEqual
    subst point
    exact lastFresh pointMember
  · intro segment segmentMember _segmentAligned contains
    rcases
        GridSegment.interiorContains_or_eq_start_or_eq_finish_of_contains
          contains with
      interior | endpoint
    · exact simple.2.1 last lastMember segment
        (gridPolylineSegments_dropLast_subset route segmentMember)
        interior
    · have endpoints :=
        gridPolylineSegments_endpoints_mem segmentMember
      rcases endpoint with atStart | atFinish
      · exact lastFresh (atStart.symm ▸ endpoints.1)
      · exact lastFresh (atFinish.symm ▸ endpoints.2)

/-- Magnification and subdivision preserve the head of every nonempty old
route. -/
theorem magnifiedUnitRoute_head?_of_cons
    (first : Cell) (rest : List Cell) :
    (magnifiedUnitRoute (first :: rest)).head? =
      some (normalizeVertexPosition first) := by
  unfold magnifiedUnitRoute
  rw [AxisDirection.unitSubdividePolyline_head? (by simp)]
  simp

/-- Magnification and subdivision preserve the last endpoint of every
nonempty orthogonal route. -/
theorem magnifiedUnitRoute_getLast?
    {points : List Cell}
    (nonempty : points ≠ [])
    (orthogonal : OrthogonalPolyline points) :
    (magnifiedUnitRoute points).getLast? =
      points.getLast?.map normalizeVertexPosition := by
  have mappedOrthogonal :
      OrthogonalPolyline (points.map normalizeVertexPosition) := by
    rw [map_normalizeVertexPosition_eq_translate_scalePolyline]
    have scaled : OrthogonalPolyline
        (scalePolyline vertexNormalizationScale points) := by
      simpa [vertexNormalizationScale] using
        OrthogonalPolyline.scalePolyline orthogonal
          (factor := 12) (by norm_num)
    exact scaled.translate center
  unfold magnifiedUnitRoute
  rw [AxisDirection.unitSubdividePolyline_getLast?
    (by simpa using nonempty)]
  · simp [List.getLast?_map]
  · exact mappedOrthogonal

/-- After dropping three entries inside the first scaled segment, the full
magnified route is the endpoint join of that remaining radial segment and
the magnified old tail. -/
theorem magnifiedUnitRoute_drop_three_cons_cons
    (first second : Cell) (rest : List Cell)
    (aligned : (GridSegment.mk first second).IsAxisAligned) :
    (magnifiedUnitRoute (first :: second :: rest)).drop 3 =
      joinAtEndpoint
        ((AxisDirection.unitSegmentPoints
          (normalizeVertexPosition first)
          (normalizeVertexPosition second)).drop 3)
        (magnifiedUnitRoute (second :: rest)) := by
  have oldPositive :=
    AxisDirection.segmentLength_positive_of_axisAligned aligned
  have firstSegmentLong :
      3 ≤ (AxisDirection.unitSegmentPoints
        (normalizeVertexPosition first)
        (normalizeVertexPosition second)).length := by
    simp only [AxisDirection.unitSegmentPoints_length,
      segmentLength_normalizeVertexPosition]
    omega
  unfold magnifiedUnitRoute
  simp only [List.map_cons]
  rw [AxisDirection.unitSubdividePolyline]
  unfold joinAtEndpoint
  rw [List.drop_append_of_le_length firstSegmentLong]

/-- The radial piece left by the three-point trim ends at the normalized
second old route point. -/
theorem unitSegmentPoints_drop_three_getLast?
    {first second : Cell}
    (aligned : (GridSegment.mk first second).IsAxisAligned) :
    ((AxisDirection.unitSegmentPoints
      (normalizeVertexPosition first)
      (normalizeVertexPosition second)).drop 3).getLast? =
        some (normalizeVertexPosition second) := by
  have oldPositive :=
    AxisDirection.segmentLength_positive_of_axisAligned aligned
  have within :
      3 < (AxisDirection.unitSegmentPoints
        (normalizeVertexPosition first)
        (normalizeVertexPosition second)).length := by
    simp only [AxisDirection.unitSegmentPoints_length,
      segmentLength_normalizeVertexPosition]
    omega
  rw [List.getLast?_drop_eq_getLast?_of_lt within]
  have normalizedAligned :
      (GridSegment.mk
        (normalizeVertexPosition first)
        (normalizeVertexPosition second)).IsAxisAligned := by
    have scaledAligned :
        (GridSegment.scale vertexNormalizationScale
          (GridSegment.mk first second)).IsAxisAligned :=
      (GridSegment.isAxisAligned_scale_iff
        (by norm_num [vertexNormalizationScale])
        (GridSegment.mk first second)).2 aligned
    have translatedAligned :=
      (GridSegment.isAxisAligned_translate
        (GridSegment.scale vertexNormalizationScale
          (GridSegment.mk first second)) center).2 scaledAligned
    simpa [GridSegment.scale, GridSegment.translate,
      normalizeVertexPosition, Cell.add_comm] using translatedAligned
  exact AxisDirection.unitSegmentPoints_getLast?
    normalizedAligned

/-- At a source endpoint, the trimmed magnified corridor strictly avoids
every Figure 2 arm assigned to a different port at the same old vertex. -/
theorem trimmedMagnifiedRoute_strictlyAvoids_incident_otherTemplate
    (first second : Cell) (rest : List Cell)
    (simple : LocalIncidenceDrawing.RouteIsSimple
      (first :: second :: rest))
    (orthogonal : OrthogonalPolyline (first :: second :: rest))
    (side : VertexSide)
    (direction : AxisDirection.between first second = side.direction)
    (omitted : VertexSide) (used : side ≠ omitted)
    (otherPort : CanonicalVertexPort)
    (different : otherPort ≠ canonicalPortForSide omitted side) :
    RoutesStrictlyAvoidEachOther
      (trimmedMagnifiedRoute (first :: second :: rest))
      (normalizationTemplateAt first (route omitted otherPort)) := by
  have aligned : (GridSegment.mk first second).IsAxisAligned :=
    (List.isChain_cons_cons.mp orthogonal).1
  let radial :=
    (AxisDirection.unitSegmentPoints
      (normalizeVertexPosition first)
      (normalizeVertexPosition second)).drop 3
  have radialBound :
      ∀ point ∈ radial,
        Cell.linearValue side.direction.step
            (normalizeVertexPosition first) + 2 <
          Cell.linearValue side.direction.step point := by
    exact unitSegmentPoints_drop_three_linearValue_gt side
      ((between_normalizeVertexPosition first second).trans direction)
  have templateBound :
      ∀ point ∈ normalizationTemplateAt first (route omitted otherPort),
        Cell.linearValue side.direction.step point ≤
          Cell.linearValue side.direction.step
            (normalizeVertexPosition first) + 2 :=
    normalizationTemplateAt_route_linearValue_le_center_of_port_ne_side
      first omitted side otherPort used different
  have radialStrict :
      RoutesStrictlyAvoidEachOther radial
        (normalizationTemplateAt first (route omitted otherPort)) :=
    (routesStrictlyAvoidEachOther_of_linear_separated
      side.direction.step
      (Cell.linearValue side.direction.step
        (normalizeVertexPosition first) + 2)
      templateBound radialBound).symm
  have tailAvoids :=
    LocalIncidenceDrawing.RouteIsSimple.tail_avoids_head
      (head := first) simple (by simp)
  have tailStrict :
      RoutesStrictlyAvoidEachOther
        (magnifiedUnitRoute (second :: rest))
        (normalizationTemplateAt first (route omitted otherPort)) :=
    magnifiedUnitRoute_strictlyAvoids_normalizationTemplateAt_route
      (List.isChain_cons_cons.mp orthogonal).2
      (by simpa using tailAvoids.1)
      (by
        intro segment segmentMember segmentAligned
        exact tailAvoids.2 segment
          (by simpa using segmentMember) segmentAligned)
      omitted otherPort
  have joinedStrict :
      RoutesStrictlyAvoidEachOther
        (joinAtEndpoint radial (magnifiedUnitRoute (second :: rest)))
        (normalizationTemplateAt first (route omitted otherPort)) := by
    apply radialStrict.join_left tailStrict
    · exact unitSegmentPoints_drop_three_getLast? aligned
    · exact magnifiedUnitRoute_head?_of_cons second rest
  have dropped :=
    magnifiedUnitRoute_drop_three_cons_cons first second rest aligned
  change RoutesStrictlyAvoidEachOther
    ((magnifiedUnitRoute (first :: second :: rest)).drop 3 |>.take
      ((magnifiedUnitRoute (first :: second :: rest)).length - 6))
    (normalizationTemplateAt first (route omitted otherPort))
  rw [dropped]
  exact joinedStrict.take_left
    ((magnifiedUnitRoute (first :: second :: rest)).length - 6)

/-- The target-end form of incident corridor separation, obtained by
splitting the reversed symmetric trim at the final old segment. -/
theorem trimmedMagnifiedRoute_strictlyAvoids_incident_otherTemplate_at_target
    (leading : List Cell) (before last : Cell)
    (simple : LocalIncidenceDrawing.RouteIsSimple
      (leading ++ [before, last]))
    (orthogonal : OrthogonalPolyline (leading ++ [before, last]))
    (side : VertexSide)
    (direction : AxisDirection.between last before = side.direction)
    (omitted : VertexSide) (used : side ≠ omitted)
    (otherPort : CanonicalVertexPort)
    (different : otherPort ≠ canonicalPortForSide omitted side) :
    RoutesStrictlyAvoidEachOther
      (trimmedMagnifiedRoute (leading ++ [before, last]))
      (normalizationTemplateAt last (route omitted otherPort)) := by
  let oldPrefix := leading ++ [before]
  let initialRoute := magnifiedUnitRoute oldPrefix
  let finalSegment := AxisDirection.unitSegmentPoints
    (normalizeVertexPosition before) (normalizeVertexPosition last)
  let radial := finalSegment.reverse.drop 3
  have aligned : (GridSegment.mk before last).IsAxisAligned :=
    (List.isChain_append_cons_cons.mp orthogonal).2.1
  have prefixOrthogonal : OrthogonalPolyline oldPrefix := by
    exact (List.isChain_append_cons_cons.mp orthogonal).1
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
  have radialBound :
      ∀ point ∈ radial,
        Cell.linearValue side.direction.step
            (normalizeVertexPosition last) + 2 <
          Cell.linearValue side.direction.step point := by
    exact unitSegmentPoints_reverse_drop_three_linearValue_gt
      side normalizedAligned
        ((between_normalizeVertexPosition last before).trans direction)
  have templateBound :
      ∀ point ∈ normalizationTemplateAt last (route omitted otherPort),
        Cell.linearValue side.direction.step point ≤
          Cell.linearValue side.direction.step
            (normalizeVertexPosition last) + 2 :=
    normalizationTemplateAt_route_linearValue_le_center_of_port_ne_side
      last omitted side otherPort used different
  have radialStrict :
      RoutesStrictlyAvoidEachOther radial
        (normalizationTemplateAt last (route omitted otherPort)) :=
    (routesStrictlyAvoidEachOther_of_linear_separated
      side.direction.step
      (Cell.linearValue side.direction.step
        (normalizeVertexPosition last) + 2)
      templateBound radialBound).symm
  have prefixAvoids :=
    LocalIncidenceDrawing.RouteIsSimple.dropLast_avoids_last
      (last := last) simple (by simp)
  have initialStrict :
      RoutesStrictlyAvoidEachOther initialRoute
        (normalizationTemplateAt last (route omitted otherPort)) := by
    apply magnifiedUnitRoute_strictlyAvoids_normalizationTemplateAt_route
      prefixOrthogonal
    · simpa [oldPrefix] using prefixAvoids.1
    · intro segment segmentMember segmentAligned
      exact prefixAvoids.2 segment
        (by simpa [oldPrefix] using segmentMember) segmentAligned
  have initialReverseStrict :
      RoutesStrictlyAvoidEachOther initialRoute.reverse
        (normalizationTemplateAt last (route omitted otherPort)) :=
    initialStrict.reverse_left
  have prefixLast : oldPrefix.getLast? = some before := by
    simp [oldPrefix]
  have initialLast :
      initialRoute.getLast? = some (normalizeVertexPosition before) := by
    have preserved := magnifiedUnitRoute_getLast?
      (points := oldPrefix) (by simp [oldPrefix]) prefixOrthogonal
    simpa [initialRoute, oldPrefix, prefixLast] using preserved
  have finalHead :
      finalSegment.head? = some (normalizeVertexPosition before) := by
    exact AxisDirection.unitSegmentPoints_head? _ _
  have finalLast :
      finalSegment.getLast? = some (normalizeVertexPosition last) := by
    exact AxisDirection.unitSegmentPoints_getLast? normalizedAligned
  have finalLong : 3 < finalSegment.length := by
    simp only [finalSegment, AxisDirection.unitSegmentPoints_length,
      segmentLength_normalizeVertexPosition]
    have positive :=
      AxisDirection.segmentLength_positive_of_axisAligned aligned
    omega
  have radialLast :
      radial.getLast? = some (normalizeVertexPosition before) := by
    unfold radial
    rw [List.getLast?_drop_eq_getLast?_of_lt]
    · simp [finalSegment]
    · simpa [List.length_reverse] using finalLong
  have initialReverseHead :
      initialRoute.reverse.head? =
        some (normalizeVertexPosition before) := by
    simpa using initialLast
  have joinedStrict :
      RoutesStrictlyAvoidEachOther
        (joinAtEndpoint radial initialRoute.reverse)
        (normalizationTemplateAt last (route omitted otherPort)) := by
    exact radialStrict.join_left initialReverseStrict
      radialLast initialReverseHead
  have magnifiedEquation :
      magnifiedUnitRoute (leading ++ [before, last]) =
        joinAtEndpoint initialRoute finalSegment := by
    unfold magnifiedUnitRoute
    simp only [List.map_append, List.map_cons, List.map_nil]
    rw [unitSubdividePolyline_append_pair]
    simp [initialRoute, oldPrefix, finalSegment, magnifiedUnitRoute]
  have reversedMagnifiedEquation :
      (magnifiedUnitRoute (leading ++ [before, last])).reverse =
        joinAtEndpoint finalSegment.reverse initialRoute.reverse := by
    rw [magnifiedEquation]
    exact joinAtEndpoint_reverse initialLast finalHead
  have droppedReversedEquation :
      (magnifiedUnitRoute
        (leading ++ [before, last])).reverse.drop 3 =
        joinAtEndpoint radial initialRoute.reverse := by
    rw [reversedMagnifiedEquation]
    unfold radial joinAtEndpoint
    rw [List.drop_append_of_le_length]
    simpa [List.length_reverse] using le_of_lt finalLong
  have reversedTrimEquation :
      (trimmedMagnifiedRoute
        (leading ++ [before, last])).reverse =
        ((magnifiedUnitRoute
          (leading ++ [before, last])).reverse.drop 3).take
            ((magnifiedUnitRoute
              (leading ++ [before, last])).length - 6) := by
    unfold trimmedMagnifiedRoute
    exact (List.symmetricTrim_reverse
      (magnifiedUnitRoute (leading ++ [before, last]))).symm
  have reversedStrict :
      RoutesStrictlyAvoidEachOther
        (trimmedMagnifiedRoute
          (leading ++ [before, last])).reverse
        (normalizationTemplateAt last (route omitted otherPort)) := by
    rw [reversedTrimEquation, droppedReversedEquation]
    exact joinedStrict.take_left
      ((magnifiedUnitRoute
        (leading ++ [before, last])).length - 6)
  simpa using reversedStrict.reverse_left

end PeriodicThreeDM
end LeanTrominoes
