import LeanTrominoes.PeriodicThreeDMVertexNormalizationEndpointOccurrences
import LeanTrominoes.PeriodicThreeDMVertexNormalizationLocalTemplateSeparation
import LeanTrominoes.OrthogonalPolylineTailEndpointContactSeparation

/-!
# Separation of lifted first-round template occurrences

This module upgrades the finite Figure 2 separation checks to arbitrary
lifted endpoint occurrences.  Two distinct endpoint occurrences either have
different occurrence keys, hence different template centers, or share one
lifted contracted vertex while selecting different canonical ports.  The
source traversal can therefore meet only at template heads; reversing target
templates changes this to tail-only contact.
-/

namespace LeanTrominoes

open PeriodicOrthocrossing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
open DegreeThreeVertexNormalization

namespace PeriodicThreeDM

/-- The anchored first-round Figure 2 arm belonging to one lifted contracted
endpoint occurrence. -/
def PlanarPresentation.firstNormalizationTemplateOccurrence
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (endpoint : ContractedEndpoint) (routeTranslate : Cell) : List Cell :=
  normalizationTemplateAt
    (presentation.contractedEndpointOccurrencePosition
      endpoint routeTranslate)
    (endpoint.firstNormalizationTemplate presentation)

/-- Strict separation vacuously implies that every listed contact is at the
two route heads. -/
theorem routesMeetOnlyAtHeads_of_strict
    {first second : List Cell}
    (strict : RoutesStrictlyAvoidEachOther first second) :
    RoutesMeetOnlyAtHeads first second := by
  intro firstPoint firstMember secondPoint secondMember equal
  exact
    (strict.2.2.2 firstPoint firstMember
      secondPoint secondMember equal).elim

/-- Reversing two head-contacting routes turns their possible common head
into a possible common tail. -/
theorem routesMeetOnlyAtTails_reverse
    {first second : List Cell}
    (contacts : RoutesMeetOnlyAtHeads first second) :
    RoutesMeetOnlyAtTails first.reverse second.reverse := by
  intro firstPoint firstMember secondPoint secondMember equal
  have originalFirstMember : firstPoint ∈ first :=
    List.mem_reverse.mp firstMember
  have originalSecondMember : secondPoint ∈ second :=
    List.mem_reverse.mp secondMember
  have heads := contacts firstPoint originalFirstMember
    secondPoint originalSecondMember equal
  constructor
  · simpa [List.getLast?_reverse] using heads.1
  · simpa [List.getLast?_reverse] using heads.2

/-- Distinct lifted endpoint occurrences have separated first-round local
templates, with any listed contact confined to their common center. -/
theorem ContinuousPlanarPresentation.firstNormalizationTemplateOccurrences_avoid
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
        (planar.firstNormalizationTemplateOccurrence
          first firstTranslate)
        (planar.firstNormalizationTemplateOccurrence
          second secondTranslate) ∧
      RoutesMeetOnlyAtHeads
        (planar.firstNormalizationTemplateOccurrence
          first firstTranslate)
        (planar.firstNormalizationTemplateOccurrence
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
      planar.contractedEndpointOccurrencePosition_eq_of_key_eq keysEqual
    have localSeparation :=
      first.firstNormalizationTemplates_avoid_at_sameVertex
      presentation wellFormed degree firstMember secondMember
      endpointsDifferent verticesEqual
    unfold PlanarPresentation.firstNormalizationTemplateOccurrence
    rw [positionsEqual]
    unfold normalizationTemplateAt
    exact
      ⟨localSeparation.1.translate
          (Cell.scale vertexNormalizationScale
            (planar.contractedEndpointOccurrencePosition
              second secondTranslate)),
        localSeparation.2.translate
          (Cell.scale vertexNormalizationScale
            (planar.contractedEndpointOccurrencePosition
              second secondTranslate))⟩
  · have positionsDifferent :=
      planar.contractedEndpointOccurrencePositions_ne
        (first.vertex_mem_of_mem firstMember)
        (second.vertex_mem_of_mem secondMember)
        keysEqual
    have strict : RoutesStrictlyAvoidEachOther
        (planar.firstNormalizationTemplateOccurrence
          first firstTranslate)
        (planar.firstNormalizationTemplateOccurrence
          second secondTranslate) := by
      unfold PlanarPresentation.firstNormalizationTemplateOccurrence
        ContractedEndpoint.firstNormalizationTemplate
      exact normalizationTemplateAt_routes_strictlyAvoid_of_positions_ne
        positionsDifferent
        (omittedSideAt planar first.vertex)
        (omittedSideAt planar second.vertex)
        (first.firstNormalizedPort planar)
        (second.firstNormalizedPort planar)
    exact ⟨strict.toRoutesAvoidEachOther,
      routesMeetOnlyAtHeads_of_strict strict⟩

/-- The reversed target-template form of lifted local separation has only
tail-to-tail listed contact. -/
theorem ContinuousPlanarPresentation.reversedFirstNormalizationTemplateOccurrences_avoid
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
        (planar.firstNormalizationTemplateOccurrence
          first firstTranslate).reverse
        (planar.firstNormalizationTemplateOccurrence
          second secondTranslate).reverse ∧
      RoutesMeetOnlyAtTails
        (planar.firstNormalizationTemplateOccurrence
          first firstTranslate).reverse
        (planar.firstNormalizationTemplateOccurrence
          second secondTranslate).reverse := by
  dsimp only
  have forward :=
    presentation.firstNormalizationTemplateOccurrences_avoid
      wellFormed degree firstMember secondMember different
  exact ⟨routesAvoidEachOther_reverse forward.1,
    routesMeetOnlyAtTails_reverse forward.2⟩

end PeriodicThreeDM
end LeanTrominoes
