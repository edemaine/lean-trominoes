/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMVertexNormalizationFinalCyclicOccurrences

/-!
# Separation of final cyclic-round endpoint templates

The final round uses the same finite identity/clockwise route family as the
first cyclic round.  This module proves that the preceding port permutation
preserves distinctness and then lifts the reusable local separation facts to
arbitrary final-round endpoint occurrences.
-/

namespace LeanTrominoes

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
open DegreeThreeVertexNormalization

namespace PeriodicThreeDM

/-- Distinct endpoint ports remain distinct after the first cyclic
permutation. -/
theorem ContractedEndpoint.secondNormalizedPort_ne
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    {first second : ContractedEndpoint}
    (firstMember : first ∈ problem.contractedEndpoints)
    (secondMember : second ∈ problem.contractedEndpoints)
    (different : first ≠ second)
    (sameVertex : first.vertex = second.vertex) :
    first.secondNormalizedPort presentation.toPlanarPresentation ≠
      second.secondNormalizedPort presentation.toPlanarPresentation := by
  let planar := presentation.toPlanarPresentation
  have portsDifferent := first.firstNormalizedPort_ne
    presentation wellFormed degree firstMember secondMember
      different sameVertex
  unfold ContractedEndpoint.secondNormalizedPort
  rw [sameVertex]
  intro equal
  exact portsDifferent
    (rotationRoundPort_injective
      (firstRotationActive planar second.vertex) equal)

/-- The selected final-round templates of distinct endpoints at one vertex
avoid each other and can meet only at their common head. -/
theorem ContractedEndpoint.finalNormalizationTemplates_avoid_at_sameVertex
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
        (first.finalNormalizationTemplate planar)
        (second.finalNormalizationTemplate planar) ∧
      RoutesMeetOnlyAtHeads
        (first.finalNormalizationTemplate planar)
        (second.finalNormalizationTemplate planar) := by
  dsimp only
  let planar := presentation.toPlanarPresentation
  have portsDifferent := first.secondNormalizedPort_ne
    presentation wellFormed degree firstMember secondMember
      different sameVertex
  unfold ContractedEndpoint.finalNormalizationTemplate
  rw [sameVertex]
  exact
    ⟨rotationRoundRoutes_avoidEachOther
        (secondRotationActive planar second.vertex) portsDifferent,
      rotationRoundRoutes_meetOnlyAtHeads
        (secondRotationActive planar second.vertex) portsDifferent⟩

/-- Equal endpoint keys give equal final-round template centers. -/
theorem PlanarPresentation.normalizationEndpointOccurrencePosition2_eq_of_key_eq
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    {first second : ContractedEndpoint}
    {firstTranslate secondTranslate : Cell}
    (equal : first.occurrenceKey firstTranslate =
      second.occurrenceKey secondTranslate) :
    presentation.normalizationEndpointOccurrencePosition2
        first firstTranslate =
      presentation.normalizationEndpointOccurrencePosition2
        second secondTranslate := by
  rw [presentation.normalizationEndpointOccurrencePosition2_eq,
    presentation.normalizationEndpointOccurrencePosition2_eq]
  exact congrArg normalizeVertexPosition
    (presentation.normalizationEndpointOccurrencePosition1_eq_of_key_eq equal)

/-- Distinct lifted endpoint occurrences have separated final-round
templates, with any contact confined to their common head. -/
theorem ContinuousPlanarPresentation.finalNormalizationTemplateOccurrences_avoid
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
        (planar.finalNormalizationTemplateOccurrence
          first firstTranslate)
        (planar.finalNormalizationTemplateOccurrence
          second secondTranslate) ∧
      RoutesMeetOnlyAtHeads
        (planar.finalNormalizationTemplateOccurrence
          first firstTranslate)
        (planar.finalNormalizationTemplateOccurrence
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
      planar.normalizationEndpointOccurrencePosition2_eq_of_key_eq
        keysEqual
    have localSeparation :=
      first.finalNormalizationTemplates_avoid_at_sameVertex
        presentation wellFormed degree firstMember secondMember
        endpointsDifferent verticesEqual
    unfold PlanarPresentation.finalNormalizationTemplateOccurrence
    rw [positionsEqual]
    unfold normalizationTemplateAt
    exact
      ⟨localSeparation.1.translate
          (Cell.scale vertexNormalizationScale
            (planar.normalizationEndpointOccurrencePosition2
              second secondTranslate)),
        localSeparation.2.translate
          (Cell.scale vertexNormalizationScale
            (planar.normalizationEndpointOccurrencePosition2
              second secondTranslate))⟩
  · have positionsDifferent :
        planar.normalizationEndpointOccurrencePosition2
            first firstTranslate ≠
          planar.normalizationEndpointOccurrencePosition2
            second secondTranslate := by
      intro positionsEqual
      exact keysEqual
        (planar.normalizationEndpointOccurrencePosition2_injective
          (first.vertex_mem_of_mem firstMember)
          (second.vertex_mem_of_mem secondMember) positionsEqual)
    have strict : RoutesStrictlyAvoidEachOther
        (planar.finalNormalizationTemplateOccurrence
          first firstTranslate)
        (planar.finalNormalizationTemplateOccurrence
          second secondTranslate) := by
      unfold PlanarPresentation.finalNormalizationTemplateOccurrence
        ContractedEndpoint.finalNormalizationTemplate
      exact
        normalizationTemplateAt_rotationRoundRoutes_strictlyAvoid_of_positions_ne
          positionsDifferent
          (secondRotationActive planar first.vertex)
          (secondRotationActive planar second.vertex)
          (first.secondNormalizedPort planar)
          (second.secondNormalizedPort planar)
    exact ⟨strict.toRoutesAvoidEachOther,
      routesMeetOnlyAtHeads_of_strict strict⟩

end PeriodicThreeDM
end LeanTrominoes
