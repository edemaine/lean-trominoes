import LeanTrominoes.PeriodicThreeDMVertexNormalizationCyclicOccurrences

/-!
# Separation of first cyclic-round endpoint templates

The identity and clockwise Figure 3 route families are checked finitely.
Their routes are duplicate-free, stay within radius three of the local
center, and distinct selected ports meet only at their common head.  These
facts are then lifted to arbitrary endpoint occurrences of the first
intermediate drawing.
-/

namespace LeanTrominoes

open PeriodicEightOccurrenceSplit
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
open DegreeThreeVertexNormalization

namespace PeriodicThreeDM

/-- The port permutation selected by either cyclic-round mode is injective. -/
theorem rotationRoundPort_injective (active : Bool) :
    Function.Injective fun oldPort =>
      (rotationRoundPortAndRoute active oldPort).1 := by
  intro first second equal
  cases active <;> cases first <;> cases second <;>
    simp_all [rotationRoundPortAndRoute, newPortAfterClockwise]

/-- Every selected cyclic-round route has no repeated listed point. -/
theorem rotationRoundRoute_nodup
    (active : Bool) (oldPort : CanonicalVertexPort) :
    (rotationRoundPortAndRoute active oldPort).2.Nodup := by
  cases active <;> cases oldPort <;> native_decide

/-- Every selected cyclic-round route lies within coordinate radius three
of the local center. -/
theorem rotationRoundRoute_withinCoordinateRadius
    (active : Bool) (oldPort : CanonicalVertexPort) :
    ∀ point ∈ (rotationRoundPortAndRoute active oldPort).2,
      WithinCoordinateRadius 3 center point := by
  cases active <;> cases oldPort <;> native_decide

set_option maxHeartbeats 1000000 in
/-- Distinct inputs to one selected cyclic-round mode produce completely
separated routes. -/
theorem rotationRoundRoutes_avoidEachOther
    (active : Bool) {first second : CanonicalVertexPort}
    (different : first ≠ second) :
    RoutesAvoidEachOther
      (rotationRoundPortAndRoute active first).2
      (rotationRoundPortAndRoute active second).2 := by
  cases active <;> cases first <;> cases second <;>
    simp_all [rotationRoundPortAndRoute] <;> native_decide

/-- Any listed contact between distinct selected cyclic-round routes is at
their common local head. -/
theorem rotationRoundRoutes_meetOnlyAtHeads
    (active : Bool) {first second : CanonicalVertexPort}
    (different : first ≠ second) :
    RoutesMeetOnlyAtHeads
      (rotationRoundPortAndRoute active first).2
      (rotationRoundPortAndRoute active second).2 := by
  cases active <;> cases first <;> cases second <;>
    simp_all [rotationRoundPortAndRoute] <;> native_decide

/-- Anchoring a cyclic-round route preserves its duplicate-free point list. -/
theorem normalizationTemplateAt_rotationRoundRoute_nodup
    (position : Cell) (active : Bool)
    (oldPort : CanonicalVertexPort) :
    (normalizationTemplateAt position
      (rotationRoundPortAndRoute active oldPort).2).Nodup := by
  unfold normalizationTemplateAt
    PeriodicOrthocrossing.translatePolyline
  exact (rotationRoundRoute_nodup active oldPort).map
    (Cell.add_left_injective
      (Cell.scale vertexNormalizationScale position))

/-- An anchored cyclic-round route stays in the radius-three box around its
new center. -/
theorem normalizationTemplateAt_rotationRoundRoute_withinCoordinateRadius
    (position : Cell) (active : Bool)
    (oldPort : CanonicalVertexPort) :
    ∀ point ∈ normalizationTemplateAt position
        (rotationRoundPortAndRoute active oldPort).2,
      WithinCoordinateRadius 3
        (normalizeVertexPosition position) point := by
  intro point pointMember
  unfold normalizationTemplateAt
    PeriodicOrthocrossing.translatePolyline at pointMember
  rcases List.mem_map.mp pointMember with
    ⟨localPoint, localMember, rfl⟩
  exact
    (rotationRoundRoute_withinCoordinateRadius
      active oldPort localPoint localMember).translate
        (Cell.scale vertexNormalizationScale position)

/-- Cyclic-round templates based at distinct old positions are strictly
separated after the scale-twelve affine refinement. -/
theorem normalizationTemplateAt_rotationRoundRoutes_strictlyAvoid_of_positions_ne
    {firstPosition secondPosition : Cell}
    (positionsDifferent : firstPosition ≠ secondPosition)
    (firstActive secondActive : Bool)
    (firstPort secondPort : CanonicalVertexPort) :
    RoutesStrictlyAvoidEachOther
      (normalizationTemplateAt firstPosition
        (rotationRoundPortAndRoute firstActive firstPort).2)
      (normalizationTemplateAt secondPosition
        (rotationRoundPortAndRoute secondActive secondPort).2) := by
  apply
    routesStrictlyAvoidEachOther_of_distinct_offsetScaledCoordinateNeighborhoods
      (firstCenter := firstPosition)
      (secondCenter := secondPosition)
      (offset := center) (factor := 12) (radius := 3)
      positionsDifferent (by decide) (by decide)
  · simpa [normalizeVertexPosition, vertexNormalizationScale,
      Cell.add] using
      normalizationTemplateAt_rotationRoundRoute_withinCoordinateRadius
        firstPosition firstActive firstPort
  · simpa [normalizeVertexPosition, vertexNormalizationScale,
      Cell.add] using
      normalizationTemplateAt_rotationRoundRoute_withinCoordinateRadius
        secondPosition secondActive secondPort

/-- Distinct endpoints at one old vertex still select distinct input ports
for the first cyclic round. -/
theorem ContractedEndpoint.secondNormalizationTemplates_avoid_at_sameVertex
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    {first second : ContractedEndpoint}
    (firstMember : first ∈ problem.contractedEndpoints)
    (secondMember : second ∈ problem.contractedEndpoints)
    (different : first ≠ second)
    (sameVertex : first.vertex = second.vertex) :
    let planar := presentation.toPlanarPresentation
    RoutesAvoidEachOther
        (first.secondNormalizationTemplate planar)
        (second.secondNormalizationTemplate planar) ∧
      RoutesMeetOnlyAtHeads
        (first.secondNormalizationTemplate planar)
        (second.secondNormalizationTemplate planar) := by
  dsimp only
  let planar := presentation.toPlanarPresentation
  have portsDifferent := first.firstNormalizedPort_ne
    presentation wellFormed degree firstMember secondMember
      different sameVertex
  unfold ContractedEndpoint.secondNormalizationTemplate
  rw [sameVertex]
  exact
    ⟨rotationRoundRoutes_avoidEachOther
        (firstRotationActive planar second.vertex) portsDifferent,
      rotationRoundRoutes_meetOnlyAtHeads
        (firstRotationActive planar second.vertex) portsDifferent⟩

/-- Equal endpoint keys give equal first-stage cyclic-template centers. -/
theorem PlanarPresentation.normalizationEndpointOccurrencePosition1_eq_of_key_eq
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    {first second : ContractedEndpoint}
    {firstTranslate secondTranslate : Cell}
    (equal : first.occurrenceKey firstTranslate =
      second.occurrenceKey secondTranslate) :
    presentation.normalizationEndpointOccurrencePosition1
        first firstTranslate =
      presentation.normalizationEndpointOccurrencePosition1
        second secondTranslate := by
  rw [presentation.normalizationEndpointOccurrencePosition1_eq,
    presentation.normalizationEndpointOccurrencePosition1_eq]
  exact congrArg normalizeVertexPosition
    (presentation.contractedEndpointOccurrencePosition_eq_of_key_eq equal)

/-- Distinct lifted endpoint occurrences have separated first cyclic-round
templates, with any contact confined to their common head. -/
theorem ContinuousPlanarPresentation.secondNormalizationTemplateOccurrences_avoid
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    {first second : ContractedEndpoint}
    (firstMember : first ∈ problem.contractedEndpoints)
    (secondMember : second ∈ problem.contractedEndpoints)
    {firstTranslate secondTranslate : Cell}
    (different : (first, firstTranslate) ≠
      (second, secondTranslate)) :
    let planar := presentation.toPlanarPresentation
    RoutesAvoidEachOther
        (planar.secondNormalizationTemplateOccurrence
          first firstTranslate)
        (planar.secondNormalizationTemplateOccurrence
          second secondTranslate) ∧
      RoutesMeetOnlyAtHeads
        (planar.secondNormalizationTemplateOccurrence
          first firstTranslate)
        (planar.secondNormalizationTemplateOccurrence
          second secondTranslate) := by
  dsimp only
  let planar := presentation.toPlanarPresentation
  by_cases keysEqual : first.occurrenceKey firstTranslate =
      second.occurrenceKey secondTranslate
  · have endpointsDifferent : first ≠ second := by
      intro endpointsEqual
      subst second
      have translatesEqual :=
        first.occurrenceKey_injective_for_endpoint keysEqual
      exact different (Prod.ext rfl translatesEqual)
    have verticesEqual : first.vertex = second.vertex :=
      congrArg Prod.fst keysEqual
    have positionsEqual :=
      planar.normalizationEndpointOccurrencePosition1_eq_of_key_eq
        keysEqual
    have localSeparation :=
      first.secondNormalizationTemplates_avoid_at_sameVertex
        presentation wellFormed degree firstMember secondMember
        endpointsDifferent verticesEqual
    unfold PlanarPresentation.secondNormalizationTemplateOccurrence
    rw [positionsEqual]
    unfold normalizationTemplateAt
    exact
      ⟨localSeparation.1.translate
          (Cell.scale vertexNormalizationScale
            (planar.normalizationEndpointOccurrencePosition1
              second secondTranslate)),
        localSeparation.2.translate
          (Cell.scale vertexNormalizationScale
            (planar.normalizationEndpointOccurrencePosition1
              second secondTranslate))⟩
  · have positionsDifferent :
        planar.normalizationEndpointOccurrencePosition1
            first firstTranslate ≠
          planar.normalizationEndpointOccurrencePosition1
            second secondTranslate := by
      intro positionsEqual
      exact keysEqual
        (planar.normalizationEndpointOccurrencePosition1_injective
          (first.vertex_mem_of_mem firstMember)
          (second.vertex_mem_of_mem secondMember) positionsEqual)
    have strict : RoutesStrictlyAvoidEachOther
        (planar.secondNormalizationTemplateOccurrence
          first firstTranslate)
        (planar.secondNormalizationTemplateOccurrence
          second secondTranslate) := by
      unfold PlanarPresentation.secondNormalizationTemplateOccurrence
        ContractedEndpoint.secondNormalizationTemplate
      exact
        normalizationTemplateAt_rotationRoundRoutes_strictlyAvoid_of_positions_ne
          positionsDifferent
          (firstRotationActive planar first.vertex)
          (firstRotationActive planar second.vertex)
          (first.firstNormalizedPort planar)
          (second.firstNormalizedPort planar)
    exact ⟨strict.toRoutesAvoidEachOther,
      routesMeetOnlyAtHeads_of_strict strict⟩

end PeriodicThreeDM
end LeanTrominoes
