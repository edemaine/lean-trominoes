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

/-! ## Template boundaries -/

/-- Every side midpoint is three cardinal steps from the template center. -/
theorem boundaryPoint_eq_center_add_three_steps (side : VertexSide) :
    boundaryPoint side =
      Cell.add center (Cell.scale 3 side.direction.step) := by
  cases side <;> rfl

/-- A selected cyclic-rotation route ends at the boundary corresponding to
its incoming old port. -/
theorem rotationRoundPortAndRoute_getLast?
    (active : Bool) (oldPort : CanonicalVertexPort) :
    (rotationRoundPortAndRoute active oldPort).2.getLast? =
      some (Cell.add center
        (Cell.scale 3 oldPort.direction.step)) := by
  cases active <;> cases oldPort <;> native_decide

/-- The first normalization template ends three steps along its endpoint's
actual old side. -/
theorem ContractedEndpoint.firstNormalizationTemplate_getLast?
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (endpoint : ContractedEndpoint)
    (used : endpoint.outwardSide presentation ≠
      omittedSideAt presentation endpoint.vertex) :
    (endpoint.firstNormalizationTemplate presentation).getLast? =
      some (Cell.add center (Cell.scale 3
        (endpoint.outwardSide presentation).direction.step)) := by
  unfold ContractedEndpoint.firstNormalizationTemplate
  rw [(route_endpoints
    (omittedSideAt presentation endpoint.vertex)
    (endpoint.firstNormalizedPort presentation)).2]
  rw [boundaryPoint_eq_center_add_three_steps]
  rw [ContractedEndpoint.firstNormalizedPort,
    boundarySide_canonicalPortForSide _ _ used]

/-- The first normalization template is a unit-step chain. -/
theorem ContractedEndpoint.firstNormalizationTemplate_unitSteps
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (endpoint : ContractedEndpoint) :
    (endpoint.firstNormalizationTemplate presentation).IsChain
      AxisDirection.IsUnitAxisStep := by
  exact route_unitSteps
    (omittedSideAt presentation endpoint.vertex)
    (endpoint.firstNormalizedPort presentation)

/-- The first cyclic round ends three steps along the incoming first-round
port. -/
theorem ContractedEndpoint.secondNormalizationTemplate_getLast?
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (endpoint : ContractedEndpoint) :
    (endpoint.secondNormalizationTemplate presentation).getLast? =
      some (Cell.add center (Cell.scale 3
        (endpoint.firstNormalizedPort presentation).direction.step)) := by
  simpa [ContractedEndpoint.secondNormalizationTemplate] using
    rotationRoundPortAndRoute_getLast?
      (firstRotationActive presentation endpoint.vertex)
      (endpoint.firstNormalizedPort presentation)

/-- The final cyclic round ends three steps along the incoming second-round
port. -/
theorem ContractedEndpoint.finalNormalizationTemplate_getLast?
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (endpoint : ContractedEndpoint) :
    (endpoint.finalNormalizationTemplate presentation).getLast? =
      some (Cell.add center (Cell.scale 3
        (endpoint.secondNormalizedPort presentation).direction.step)) := by
  simpa [ContractedEndpoint.finalNormalizationTemplate] using
    rotationRoundPortAndRoute_getLast?
      (secondRotationActive presentation endpoint.vertex)
      (endpoint.secondNormalizedPort presentation)

/-- Translating a center-rooted template transports its three-step boundary
to the corresponding normalized old endpoint. -/
theorem normalizationTemplateAt_getLast?_of_three_steps
    (position : Cell) {template : List Cell}
    {direction : AxisDirection}
    (last : template.getLast? =
      some (Cell.add center (Cell.scale 3 direction.step))) :
    (normalizationTemplateAt position template).getLast? =
      some (Cell.add (normalizeVertexPosition position)
        (Cell.scale 3 direction.step)) := by
  simp [normalizationTemplateAt,
    PeriodicOrthocrossing.translatePolyline, last,
    normalizeVertexPosition, Cell.add_assoc]

/-! ## Generic normalization-round validity -/

/-- Endpoint lookups are enough to apply the explicit source trimming
formula without exposing the route's tail in the caller. -/
theorem trimmedMagnifiedRoute_head?_of_endpoints
    (points : List Cell) {first second : Cell}
    (head : points.head? = some first)
    (next : points.tail.head? = some second)
    (aligned : (GridSegment.mk first second).IsAxisAligned) :
    (trimmedMagnifiedRoute points).head? =
      some (Cell.add (normalizeVertexPosition first)
        (Cell.scale 3 (AxisDirection.between first second).step)) := by
  cases points with
  | nil => simp at head
  | cons actualFirst rest =>
      cases rest with
      | nil => simp at next
      | cons actualSecond rest =>
          have firstEqual : actualFirst = first := Option.some.inj head
          have secondEqual : actualSecond = second := by
            simpa using Option.some.inj next
          subst actualFirst
          subst actualSecond
          exact trimmedMagnifiedRoute_head?_of_cons_cons
            first second rest aligned

/-- Final and reverse-tail lookups similarly feed the explicit target
trimming formula. -/
theorem trimmedMagnifiedRoute_getLast?_of_endpoints
    (points : List Cell) {before last : Cell}
    (lastLookup : points.getLast? = some last)
    (beforeLookup : points.reverse.tail.head? = some before)
    (aligned : (GridSegment.mk before last).IsAxisAligned) :
    (trimmedMagnifiedRoute points).getLast? =
      some (Cell.add (normalizeVertexPosition last)
        (Cell.scale 3 (AxisDirection.between last before).step)) := by
  have reverseLength : 2 ≤ points.reverse.length :=
    List.two_le_length_of_tail_head?_eq_some beforeLookup
  have length : 2 ≤ points.length := by simpa using reverseLength
  obtain ⟨leading, actualBefore, actualLast, equation⟩ :=
    AxisDirection.exists_eq_append_pair_of_length_ge_two length
  have lastEqual : actualLast = last := by
    rw [equation] at lastLookup
    apply Option.some.inj
    simpa using lastLookup
  have beforeEqual : actualBefore = before := by
    rw [equation] at beforeLookup
    apply Option.some.inj
    simpa using beforeLookup
  subst actualLast
  subst actualBefore
  rw [equation]
  exact trimmedMagnifiedRoute_getLast?_of_append_pair
    leading before last aligned

/-- Reversing a unit-step chain yields another unit-step chain. -/
theorem unitSteps_reverse {points : List Cell}
    (unitSteps : points.IsChain AxisDirection.IsUnitAxisStep) :
    points.reverse.IsChain AxisDirection.IsUnitAxisStep := by
  rw [List.isChain_reverse]
  exact unitSteps.imp fun _ _ step => step.symm

/-- A normalization round is a unit-step route once the incoming route and
the two template boundaries advertise matching endpoint directions. -/
theorem normalizeRouteWithTemplates_unitSteps
    (sourcePosition targetPosition : Cell)
    (sourceTemplate targetTemplate oldRoute : List Cell)
    {sourceNext targetBefore : Cell}
    {sourceDirection targetDirection : AxisDirection}
    (oldOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline oldRoute)
    (oldHead : oldRoute.head? = some sourcePosition)
    (oldSourceNext : oldRoute.tail.head? = some sourceNext)
    (oldTarget : oldRoute.getLast? = some targetPosition)
    (oldTargetBefore : oldRoute.reverse.tail.head? = some targetBefore)
    (sourceAligned :
      (GridSegment.mk sourcePosition sourceNext).IsAxisAligned)
    (targetAligned :
      (GridSegment.mk targetBefore targetPosition).IsAxisAligned)
    (sourceDirectionEq :
      AxisDirection.between sourcePosition sourceNext = sourceDirection)
    (targetDirectionEq :
      AxisDirection.between targetPosition targetBefore = targetDirection)
    (sourceUnitSteps :
      sourceTemplate.IsChain AxisDirection.IsUnitAxisStep)
    (targetUnitSteps :
      targetTemplate.IsChain AxisDirection.IsUnitAxisStep)
    (sourceLast : sourceTemplate.getLast? =
      some (Cell.add center (Cell.scale 3 sourceDirection.step)))
    (targetLast : targetTemplate.getLast? =
      some (Cell.add center (Cell.scale 3 targetDirection.step))) :
    (normalizeRouteWithTemplates sourcePosition targetPosition
      sourceTemplate targetTemplate oldRoute).IsChain
        AxisDirection.IsUnitAxisStep := by
  let sourceRoute := normalizationTemplateAt sourcePosition sourceTemplate
  let middleRoute := trimmedMagnifiedRoute oldRoute
  let targetRoute :=
    (normalizationTemplateAt targetPosition targetTemplate).reverse
  have sourceRouteUnitSteps :
      sourceRoute.IsChain AxisDirection.IsUnitAxisStep :=
    normalizationTemplateAt_unitSteps sourcePosition sourceUnitSteps
  have middleRouteUnitSteps :
      middleRoute.IsChain AxisDirection.IsUnitAxisStep :=
    trimmedMagnifiedRoute_unitSteps oldOrthogonal
  have targetRouteUnitSteps :
      targetRoute.IsChain AxisDirection.IsUnitAxisStep := by
    apply unitSteps_reverse
    exact normalizationTemplateAt_unitSteps targetPosition targetUnitSteps
  have sourceRouteLast : sourceRoute.getLast? =
      some (Cell.add (normalizeVertexPosition sourcePosition)
        (Cell.scale 3 sourceDirection.step)) :=
    normalizationTemplateAt_getLast?_of_three_steps
      sourcePosition sourceLast
  have middleRouteHead : middleRoute.head? =
      some (Cell.add (normalizeVertexPosition sourcePosition)
        (Cell.scale 3 sourceDirection.step)) := by
    rw [← sourceDirectionEq]
    exact trimmedMagnifiedRoute_head?_of_endpoints
      oldRoute oldHead oldSourceNext sourceAligned
  have middleRouteLast : middleRoute.getLast? =
      some (Cell.add (normalizeVertexPosition targetPosition)
        (Cell.scale 3 targetDirection.step)) := by
    rw [← targetDirectionEq]
    exact trimmedMagnifiedRoute_getLast?_of_endpoints
      oldRoute oldTarget oldTargetBefore targetAligned
  have targetRouteHead : targetRoute.head? =
      some (Cell.add (normalizeVertexPosition targetPosition)
        (Cell.scale 3 targetDirection.step)) := by
    simp only [targetRoute, List.head?_reverse]
    exact normalizationTemplateAt_getLast?_of_three_steps
      targetPosition targetLast
  have innerRouteHead :
      (joinAtEndpoint middleRoute targetRoute).head? =
        some (Cell.add (normalizeVertexPosition sourcePosition)
          (Cell.scale 3 sourceDirection.step)) :=
    joinAtEndpoint_head? middleRouteHead
  unfold normalizeRouteWithTemplates
  exact List.IsChain.joinAtEndpoint sourceRouteUnitSteps
    (List.IsChain.joinAtEndpoint middleRouteUnitSteps targetRouteUnitSteps
      middleRouteLast targetRouteHead)
    sourceRouteLast innerRouteHead

/-! ## Concrete first normalization round -/

/-- Every endpoint belonging to a certified contracted fan uses one of its
three occupied sides, hence not the selected fourth side. -/
theorem ContractedVertexFan.endpoint_outwardSide_ne_omittedSideAt
    {problem : PeriodicThreeDM}
    {presentation : problem.ContinuousPlanarPresentation}
    {vertex : PeriodicThreeDMVertex}
    (fan : ContractedVertexFan presentation vertex)
    {endpoint : ContractedEndpoint}
    (member : endpoint ∈ [fan.first, fan.second, fan.third]) :
    endpoint.outwardSide presentation.toPlanarPresentation ≠
      omittedSideAt presentation.toPlanarPresentation vertex := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with first | second | third
  · subst endpoint
    rw [fan.omittedSideAt_eq]
    exact fan.coloredFan.omitted_not_first.symm
  · subst endpoint
    rw [fan.omittedSideAt_eq]
    exact fan.coloredFan.omitted_not_second.symm
  · subst endpoint
    rw [fan.omittedSideAt_eq]
    exact fan.coloredFan.omitted_not_third.symm

/-- Every enumerated endpoint uses a nonomitted side in the executable
normalization data. -/
theorem ContractedEndpoint.outwardSide_ne_omittedSideAt
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    {endpoint : ContractedEndpoint}
    (member : endpoint ∈ problem.contractedEndpoints) :
    endpoint.outwardSide presentation.toPlanarPresentation ≠
      omittedSideAt presentation.toPlanarPresentation endpoint.vertex := by
  have vertexMember := endpoint.vertex_mem_of_mem member
  cases vertexEquation : endpoint.vertex with
  | triple tripleIndex =>
      have indexLt : tripleIndex < problem.triples.length := by
        rw [vertexEquation] at vertexMember
        simpa [contractedGraph, tripleVertices,
          contractedElementVertices,
          contractedElementVerticesForColor] using vertexMember
      obtain ⟨fan⟩ := exists_contractVertexFan_at_triple
        presentation wellFormed degree tripleIndex indexLt
      have endpointAt : endpoint ∈
          problem.contractedEndpointsAt (.triple tripleIndex) :=
        (contractedEndpointsAt_mem_iff problem _ endpoint).2
          ⟨member, vertexEquation⟩
      have fanMember : endpoint ∈ [fan.first, fan.second, fan.third] := by
        rw [← fan.endpoints_eq]
        exact endpointAt
      simpa [vertexEquation] using
        fan.endpoint_outwardSide_ne_omittedSideAt fanMember
  | element color atom =>
      have atomData :
          atom < problem.elementCount color ∧
            problem.degree color atom = 3 := by
        rw [vertexEquation] at vertexMember
        simp [contractedGraph, tripleVertices,
          contractedElementVertices,
          contractedElementVerticesForColor,
          incidenceColors] at vertexMember
        cases color <;> simp_all
      obtain ⟨fan⟩ := exists_contractVertexFan_at_element
        presentation degree color atom atomData.1 atomData.2
      have endpointAt : endpoint ∈
          problem.contractedEndpointsAt (.element color atom) :=
        (contractedEndpointsAt_mem_iff problem _ endpoint).2
          ⟨member, vertexEquation⟩
      have fanMember : endpoint ∈ [fan.first, fan.second, fan.third] := by
        rw [← fan.endpoints_eq]
        exact endpointAt
      simpa [vertexEquation] using
        fan.endpoint_outwardSide_ne_omittedSideAt fanMember

/-- Contracted routes already use the stage-zero normalization endpoint
coordinates. -/
theorem PlanarPresentation.contractedEdgeRoute_normalizationEndpoints
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    {edge : ContractedEdge}
    (member : edge ∈ problem.contractedEdges) :
    (presentation.contractedEdgeRoute edge).head? =
        some (presentation.normalizationPosition0
          edge.toPeriodicEdge.source) ∧
      (presentation.contractedEdgeRoute edge).getLast? =
        some (presentation.normalizationTarget0 edge) := by
  have endpoints := presentation.contractedEdgeRoute_endpoints_of_mem member
  have graphEdgeMember : edge.toPeriodicEdge ∈
      problem.contractedGraph.edges :=
    List.mem_map.mpr ⟨edge, member, rfl⟩
  have endpointMembers :=
    (contractedGraph_isWellFormed problem).2 _ graphEdgeMember
  constructor
  · rw [endpoints.1]
    unfold PlanarPresentation.normalizationPosition0
    rw [presentation.contractedDrawing_vertexPosition endpointMembers.1]
  · rw [endpoints.2]
    unfold PlanarPresentation.normalizationTarget0
      PlanarPresentation.normalizationPosition0
    rw [presentation.contractedDrawing_vertexPosition endpointMembers.2]
    simp

/-- The first concrete normalization round converts every emitted
contracted edge into a unit-step route. -/
theorem ContinuousPlanarPresentation.normalizationRoute1_unitSteps
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    {edge : ContractedEdge}
    (edgeMember : edge ∈ problem.contractedEdges) :
    (presentation.toPlanarPresentation.normalizationRoute1 edge).IsChain
      AxisDirection.IsUnitAxisStep := by
  let planar := presentation.toPlanarPresentation
  let oldRoute := planar.contractedEdgeRoute edge
  let sourceEndpoint := ContractedEndpoint.source edge
  let targetEndpoint := ContractedEndpoint.target edge
  have sourceMember : sourceEndpoint ∈ problem.contractedEndpoints := by
    simp [sourceEndpoint, contractedEndpoints, edgeMember]
  have targetMember : targetEndpoint ∈ problem.contractedEndpoints := by
    simp [targetEndpoint, contractedEndpoints, edgeMember]
  have routeLength : 2 ≤ oldRoute.length :=
    planar.contractedEdgeRoute_length_ge_two degree edgeMember
  have oldOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline oldRoute :=
    planar.contractedEdgeRoute_orthogonal_of_mem edgeMember
  obtain ⟨first, second, rest, sourceEquation⟩ :=
    List.exists_eq_cons_cons_of_length_ge_two routeLength
  obtain ⟨leading, before, last, targetEquation⟩ :=
    AxisDirection.exists_eq_append_pair_of_length_ge_two routeLength
  have endpoints :=
    planar.contractedEdgeRoute_normalizationEndpoints edgeMember
  have firstEqual : first =
      planar.normalizationPosition0 edge.toPeriodicEdge.source := by
    have oldHead := endpoints.1
    change oldRoute.head? = _ at oldHead
    rw [sourceEquation] at oldHead
    exact Option.some.inj oldHead
  have lastEqual : last = planar.normalizationTarget0 edge := by
    have oldLast := endpoints.2
    change oldRoute.getLast? = _ at oldLast
    rw [targetEquation] at oldLast
    apply Option.some.inj
    simpa using oldLast
  subst first
  subst last
  have sourceAligned :
      (GridSegment.mk
        (planar.normalizationPosition0 edge.toPeriodicEdge.source)
        second).IsAxisAligned := by
    change PeriodicOrthocrossing.OrthogonalPolyline oldRoute at oldOrthogonal
    rw [sourceEquation] at oldOrthogonal
    exact (List.isChain_cons_cons.mp oldOrthogonal).1
  have targetAligned :
      (GridSegment.mk before (planar.normalizationTarget0 edge)).IsAxisAligned := by
    change PeriodicOrthocrossing.OrthogonalPolyline oldRoute at oldOrthogonal
    rw [targetEquation] at oldOrthogonal
    exact (List.isChain_append_cons_cons.mp oldOrthogonal).2.1
  have sourceDirection :
      AxisDirection.between
          (planar.normalizationPosition0 edge.toPeriodicEdge.source) second =
        (sourceEndpoint.outwardSide planar).direction := by
    rw [sourceEndpoint.outwardSide_direction planar degree sourceMember]
    change AxisDirection.between
        (planar.normalizationPosition0 edge.toPeriodicEdge.source) second =
      AxisDirection.polylineFirstDirection oldRoute
    rw [sourceEquation]
    rfl
  have targetDirection :
      AxisDirection.between (planar.normalizationTarget0 edge) before =
        (targetEndpoint.outwardSide planar).direction := by
    rw [targetEndpoint.outwardSide_direction planar degree targetMember]
    change AxisDirection.between (planar.normalizationTarget0 edge) before =
      (AxisDirection.polylineLastDirection oldRoute).opposite
    rw [targetEquation]
    rw [AxisDirection.polylineLastDirection_append_pair_of_axisAligned
      leading targetAligned]
    exact AxisDirection.between_reverse_eq_opposite
      (AxisDirection.between_isGenuine_of_axisAligned targetAligned)
  have sourceUsed := sourceEndpoint.outwardSide_ne_omittedSideAt
    presentation wellFormed degree sourceMember
  have targetUsed := targetEndpoint.outwardSide_ne_omittedSideAt
    presentation wellFormed degree targetMember
  unfold PlanarPresentation.normalizationRoute1
  apply normalizeRouteWithTemplates_unitSteps
    (sourceNext := second) (targetBefore := before)
    (sourceDirection := (sourceEndpoint.outwardSide planar).direction)
    (targetDirection := (targetEndpoint.outwardSide planar).direction)
  · exact oldOrthogonal
  · change oldRoute.head? = _
    rw [sourceEquation]
    simp [planar]
  · change oldRoute.tail.head? = _
    rw [sourceEquation]
    simp
  · change oldRoute.getLast? = _
    rw [targetEquation]
    simp [planar]
  · change oldRoute.reverse.tail.head? = _
    rw [targetEquation]
    simp
  · exact sourceAligned
  · exact targetAligned
  · exact sourceDirection
  · exact targetDirection
  · exact sourceEndpoint.firstNormalizationTemplate_unitSteps planar
  · exact targetEndpoint.firstNormalizationTemplate_unitSteps planar
  · exact sourceEndpoint.firstNormalizationTemplate_getLast?
      planar sourceUsed
  · exact targetEndpoint.firstNormalizationTemplate_getLast?
      planar targetUsed

end PeriodicThreeDM
end LeanTrominoes
