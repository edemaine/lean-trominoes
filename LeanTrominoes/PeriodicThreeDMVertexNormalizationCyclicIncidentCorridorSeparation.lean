import LeanTrominoes.PeriodicThreeDMVertexNormalizationCyclicCorridorSeparation
import LeanTrominoes.PeriodicThreeDMVertexNormalizationIncidentCorridorSeparation

/-!
# Separation of incident cyclic-normalization corridors

The identity and clockwise templates used in either cyclic normalization
round stay behind the hyperplane two steps from the center in every incoming
port direction other than their own.  The symmetric trim of an incident
magnified route starts beyond that hyperplane.  This gives strict separation
at an incident endpoint; the rest of the old route is remote and is handled
by the common scale-twelve neighborhood argument.
-/

namespace LeanTrominoes

open PeriodicEightOccurrenceSplit
open PeriodicOrthocrossing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
open DegreeThreeVertexNormalization

namespace CanonicalVertexPort

/-- The corresponding old-style vertex side, used by the directional
linear-separation API. -/
def vertexSide : CanonicalVertexPort → VertexSide
  | .west => .west
  | .north => .north
  | .east => .east

@[simp]
theorem vertexSide_direction (port : CanonicalVertexPort) :
    port.vertexSide.direction = port.direction := by
  cases port <;> rfl

end CanonicalVertexPort

namespace PeriodicThreeDM

/-- A selected cyclic template for a different incoming port stays no more
than two steps beyond the center in the owning port's direction. -/
theorem rotationRoundRoute_linearValue_le_center_of_port_ne
    (active : Bool) {oldPort otherPort : CanonicalVertexPort}
    (different : otherPort ≠ oldPort) :
    ∀ point ∈ (rotationRoundPortAndRoute active otherPort).2,
      Cell.linearValue oldPort.direction.step point ≤
        Cell.linearValue oldPort.direction.step center + 2 := by
  cases active <;> cases oldPort <;> cases otherPort <;>
    simp_all [rotationRoundPortAndRoute, newPortAfterClockwise,
      identityRotationRoute, clockwiseRotationRoute,
      CanonicalVertexPort.direction, AxisDirection.step,
      Cell.linearValue, center]

/-- The same cyclic-template half-plane bound after anchoring at an old
lattice point. -/
theorem normalizationTemplateAt_rotationRoundRoute_linearValue_le_center_of_port_ne
    (position : Cell) (active : Bool)
    {oldPort otherPort : CanonicalVertexPort}
    (different : otherPort ≠ oldPort) :
    ∀ point ∈ normalizationTemplateAt position
        (rotationRoundPortAndRoute active otherPort).2,
      Cell.linearValue oldPort.direction.step point ≤
        Cell.linearValue oldPort.direction.step
          (normalizeVertexPosition position) + 2 := by
  intro point pointMember
  unfold normalizationTemplateAt
    PeriodicOrthocrossing.translatePolyline at pointMember
  rcases List.mem_map.mp pointMember with
    ⟨localPoint, localMember, rfl⟩
  have localBound :=
    rotationRoundRoute_linearValue_le_center_of_port_ne
      active different localPoint localMember
  simp only [normalizeVertexPosition, Cell.linearValue_add]
  omega

/-- If an old orthogonal route is remote from a lattice point, its full
magnified unit subdivision strictly avoids either cyclic template there. -/
theorem magnifiedUnitRoute_strictlyAvoids_rotationRoundTemplate
    {oldRoute : List Cell} {position : Cell}
    (oldOrthogonal : OrthogonalPolyline oldRoute)
    (oldPointsAvoid : ∀ point ∈ oldRoute, point ≠ position)
    (oldSegmentsAvoid :
      ∀ segment ∈ gridPolylineSegments oldRoute,
        segment.IsAxisAligned → ¬segment.Contains position)
    (active : Bool) (oldPort : CanonicalVertexPort) :
    RoutesStrictlyAvoidEachOther
      (magnifiedUnitRoute oldRoute)
      (normalizationTemplateAt position
        (rotationRoundPortAndRoute active oldPort).2) := by
  have scaledStrict :=
    routesStrictlyAvoidEachOther_translateScalePolyline_pointNeighborhood
      (source := oldRoute)
      (nearby := normalizationTemplateAt position
        (rotationRoundPortAndRoute active oldPort).2)
      (center := position) (offset := center)
      (factor := 12) (radius := 3)
      (by decide) (by decide)
      oldPointsAvoid oldSegmentsAvoid
      (by
        simpa [normalizeVertexPosition, vertexNormalizationScale,
          Cell.add, add_comm] using
          normalizationTemplateAt_rotationRoundRoute_withinCoordinateRadius
            position active oldPort)
  have scaledOrthogonal :
      OrthogonalPolyline
        (translatePolyline center (scalePolyline 12 oldRoute)) :=
    (oldOrthogonal.scalePolyline (by decide)).translate center
  have templateOrthogonal :
      OrthogonalPolyline
        (normalizationTemplateAt position
          (rotationRoundPortAndRoute active oldPort).2) := by
    have localOrthogonal : OrthogonalPolyline
        (rotationRoundPortAndRoute active oldPort).2 :=
      ((rotationRoundPortAndRoute_geometry active oldPort).2.2.1).imp
        (fun _ _ step => step.isAxisAligned)
    unfold normalizationTemplateAt
    exact localOrthogonal.translate _
  rw [magnifiedUnitRoute_eq_translate_scale]
  exact scaledStrict.refine_left
    scaledOrthogonal templateOrthogonal
    (AxisDirection.unitSubdividePolyline_refines scaledOrthogonal)

/-- The remote cyclic-template result persists after the symmetric endpoint
trim used by normalized routes. -/
theorem trimmedMagnifiedRoute_strictlyAvoids_rotationRoundTemplate
    {oldRoute : List Cell} {position : Cell}
    (oldOrthogonal : OrthogonalPolyline oldRoute)
    (oldPointsAvoid : ∀ point ∈ oldRoute, point ≠ position)
    (oldSegmentsAvoid :
      ∀ segment ∈ gridPolylineSegments oldRoute,
        segment.IsAxisAligned → ¬segment.Contains position)
    (active : Bool) (oldPort : CanonicalVertexPort) :
    RoutesStrictlyAvoidEachOther
      (trimmedMagnifiedRoute oldRoute)
      (normalizationTemplateAt position
        (rotationRoundPortAndRoute active oldPort).2) := by
  have refinedStrict :=
    magnifiedUnitRoute_strictlyAvoids_rotationRoundTemplate
      oldOrthogonal oldPointsAvoid oldSegmentsAvoid active oldPort
  exact
    (refinedStrict.drop_left 3).take_left
      ((magnifiedUnitRoute oldRoute).length - 6)

/-- At a source endpoint, the trimmed magnified corridor strictly avoids a
cyclic template assigned to a different incoming port at the same center. -/
theorem trimmedMagnifiedRoute_strictlyAvoids_incident_otherRotationRoundTemplate
    (first second : Cell) (rest : List Cell)
    (simple : LocalIncidenceDrawing.RouteIsSimple
      (first :: second :: rest))
    (orthogonal : OrthogonalPolyline (first :: second :: rest))
    (oldPort otherPort : CanonicalVertexPort)
    (direction : AxisDirection.between first second = oldPort.direction)
    (active : Bool) (different : otherPort ≠ oldPort) :
    RoutesStrictlyAvoidEachOther
      (trimmedMagnifiedRoute (first :: second :: rest))
      (normalizationTemplateAt first
        (rotationRoundPortAndRoute active otherPort).2) := by
  have aligned : (GridSegment.mk first second).IsAxisAligned :=
    (List.isChain_cons_cons.mp orthogonal).1
  let radial :=
    (AxisDirection.unitSegmentPoints
      (normalizeVertexPosition first)
      (normalizeVertexPosition second)).drop 3
  have radialBound :
      ∀ point ∈ radial,
        Cell.linearValue oldPort.direction.step
            (normalizeVertexPosition first) + 2 <
          Cell.linearValue oldPort.direction.step point := by
    have directionSide :
        AxisDirection.between first second =
          oldPort.vertexSide.direction := by
      simpa using direction
    simpa using
      (unitSegmentPoints_drop_three_linearValue_gt oldPort.vertexSide
        ((between_normalizeVertexPosition first second).trans directionSide))
  have templateBound :
      ∀ point ∈ normalizationTemplateAt first
          (rotationRoundPortAndRoute active otherPort).2,
        Cell.linearValue oldPort.direction.step point ≤
          Cell.linearValue oldPort.direction.step
            (normalizeVertexPosition first) + 2 :=
    normalizationTemplateAt_rotationRoundRoute_linearValue_le_center_of_port_ne
      first active different
  have radialStrict :
      RoutesStrictlyAvoidEachOther radial
        (normalizationTemplateAt first
          (rotationRoundPortAndRoute active otherPort).2) :=
    (routesStrictlyAvoidEachOther_of_linear_separated
      oldPort.direction.step
      (Cell.linearValue oldPort.direction.step
        (normalizeVertexPosition first) + 2)
      templateBound radialBound).symm
  have tailAvoids :=
    LocalIncidenceDrawing.RouteIsSimple.tail_avoids_head
      (head := first) simple (by simp)
  have tailStrict :
      RoutesStrictlyAvoidEachOther
        (magnifiedUnitRoute (second :: rest))
        (normalizationTemplateAt first
          (rotationRoundPortAndRoute active otherPort).2) :=
    magnifiedUnitRoute_strictlyAvoids_rotationRoundTemplate
      (List.isChain_cons_cons.mp orthogonal).2
      (by simpa using tailAvoids.1)
      (by
        intro segment segmentMember segmentAligned
        exact tailAvoids.2 segment
          (by simpa using segmentMember) segmentAligned)
      active otherPort
  have joinedStrict :
      RoutesStrictlyAvoidEachOther
        (joinAtEndpoint radial (magnifiedUnitRoute (second :: rest)))
        (normalizationTemplateAt first
          (rotationRoundPortAndRoute active otherPort).2) := by
    apply radialStrict.join_left tailStrict
    · exact unitSegmentPoints_drop_three_getLast? aligned
    · exact magnifiedUnitRoute_head?_of_cons second rest
  have dropped :=
    magnifiedUnitRoute_drop_three_cons_cons first second rest aligned
  change RoutesStrictlyAvoidEachOther
    ((magnifiedUnitRoute (first :: second :: rest)).drop 3 |>.take
      ((magnifiedUnitRoute (first :: second :: rest)).length - 6))
    (normalizationTemplateAt first
      (rotationRoundPortAndRoute active otherPort).2)
  rw [dropped]
  exact joinedStrict.take_left
    ((magnifiedUnitRoute (first :: second :: rest)).length - 6)

/-- Target-end form of incident cyclic-template separation. -/
theorem trimmedMagnifiedRoute_strictlyAvoids_incident_otherRotationRoundTemplate_at_target
    (leading : List Cell) (before last : Cell)
    (simple : LocalIncidenceDrawing.RouteIsSimple
      (leading ++ [before, last]))
    (orthogonal : OrthogonalPolyline (leading ++ [before, last]))
    (oldPort otherPort : CanonicalVertexPort)
    (direction : AxisDirection.between last before = oldPort.direction)
    (active : Bool) (different : otherPort ≠ oldPort) :
    RoutesStrictlyAvoidEachOther
      (trimmedMagnifiedRoute (leading ++ [before, last]))
      (normalizationTemplateAt last
        (rotationRoundPortAndRoute active otherPort).2) := by
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
        Cell.linearValue oldPort.direction.step
            (normalizeVertexPosition last) + 2 <
          Cell.linearValue oldPort.direction.step point := by
    have directionSide :
        AxisDirection.between last before =
          oldPort.vertexSide.direction := by
      simpa using direction
    simpa using
      (unitSegmentPoints_reverse_drop_three_linearValue_gt
        oldPort.vertexSide normalizedAligned
          ((between_normalizeVertexPosition last before).trans
            directionSide))
  have templateBound :
      ∀ point ∈ normalizationTemplateAt last
          (rotationRoundPortAndRoute active otherPort).2,
        Cell.linearValue oldPort.direction.step point ≤
          Cell.linearValue oldPort.direction.step
            (normalizeVertexPosition last) + 2 :=
    normalizationTemplateAt_rotationRoundRoute_linearValue_le_center_of_port_ne
      last active different
  have radialStrict :
      RoutesStrictlyAvoidEachOther radial
        (normalizationTemplateAt last
          (rotationRoundPortAndRoute active otherPort).2) :=
    (routesStrictlyAvoidEachOther_of_linear_separated
      oldPort.direction.step
      (Cell.linearValue oldPort.direction.step
        (normalizeVertexPosition last) + 2)
      templateBound radialBound).symm
  have prefixAvoids :=
    LocalIncidenceDrawing.RouteIsSimple.dropLast_avoids_last
      (last := last) simple (by simp)
  have initialStrict :
      RoutesStrictlyAvoidEachOther initialRoute
        (normalizationTemplateAt last
          (rotationRoundPortAndRoute active otherPort).2) := by
    apply magnifiedUnitRoute_strictlyAvoids_rotationRoundTemplate
      prefixOrthogonal
    · simpa [oldPrefix] using prefixAvoids.1
    · intro segment segmentMember segmentAligned
      exact prefixAvoids.2 segment
        (by simpa [oldPrefix] using segmentMember) segmentAligned
  have initialReverseStrict :
      RoutesStrictlyAvoidEachOther initialRoute.reverse
        (normalizationTemplateAt last
          (rotationRoundPortAndRoute active otherPort).2) :=
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
        (normalizationTemplateAt last
          (rotationRoundPortAndRoute active otherPort).2) := by
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
        (normalizationTemplateAt last
          (rotationRoundPortAndRoute active otherPort).2) := by
    rw [reversedTrimEquation, droppedReversedEquation]
    exact joinedStrict.take_left
      ((magnifiedUnitRoute
        (leading ++ [before, last])).length - 6)
  simpa using reversedStrict.reverse_left

end PeriodicThreeDM
end LeanTrominoes
