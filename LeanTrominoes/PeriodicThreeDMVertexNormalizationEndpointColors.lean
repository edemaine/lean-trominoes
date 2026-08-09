import LeanTrominoes.PeriodicThreeDMVertexNormalizationRouteGeometry

/-!
# Endpoint colors after vertex normalization

The route templates permute ports but never edge identities.  This module
tracks that permutation from each endpoint's first canonical port to its
final port and proves that the transported coloring still returns the
endpoint's contracted-edge color.
-/

namespace LeanTrominoes

open Gadget
open DegreeThreeVertexNormalization

namespace PeriodicThreeDM

/-- The two executable Boolean rotation rounds implement exactly the
selected zero/one/two-step port permutation. -/
theorem ContractedEndpoint.oldPortAfterRotations_finalNormalizedPort
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (endpoint : ContractedEndpoint) :
    oldPortAfterRotations
        (rotationCountAt presentation endpoint.vertex)
        (endpoint.finalNormalizedPort presentation) =
      endpoint.firstNormalizedPort presentation := by
  generalize countEquation :
    rotationCountAt presentation endpoint.vertex = count
  generalize portEquation :
    endpoint.firstNormalizedPort presentation = port
  cases count <;> cases port <;>
    simp [ContractedEndpoint.finalNormalizedPort,
      ContractedEndpoint.secondNormalizedPort,
      rotationRoundPortAndRoute, firstRotationActive,
      secondRotationActive, countEquation, portEquation,
      oldPortAfterRotations, oldPortAfterClockwise,
      newPortAfterClockwise]

/-- Any one of a certified fan's three endpoints finds its own edge color at
the first canonical port selected from its old outward side. -/
theorem ContractedVertexFan.canonicalColoringAt_firstNormalizedPort
    {problem : PeriodicThreeDM}
    {presentation : problem.ContinuousPlanarPresentation}
    {vertex : PeriodicThreeDMVertex}
    (fan : ContractedVertexFan presentation vertex)
    (endpoint : ContractedEndpoint)
    (member : endpoint ∈ [fan.first, fan.second, fan.third]) :
    canonicalColoringAt presentation.toPlanarPresentation vertex
        (endpoint.firstNormalizedPort presentation.toPlanarPresentation) =
      endpoint.color := by
  rw [fan.canonicalColoringAt_eq]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with first | second | third
  · subst endpoint
    unfold ContractedEndpoint.firstNormalizedPort
    rw [fan.first_data.2, fan.omittedSideAt_eq]
    simpa [ContractedVertexFan.coloredFan] using
      fan.coloredFan.canonicalColoring_first
  · subst endpoint
    unfold ContractedEndpoint.firstNormalizedPort
    rw [fan.second_data.2, fan.omittedSideAt_eq]
    simpa [ContractedVertexFan.coloredFan] using
      fan.coloredFan.canonicalColoring_second
  · subst endpoint
    unfold ContractedEndpoint.firstNormalizedPort
    rw [fan.third_data.2, fan.omittedSideAt_eq]
    simpa [ContractedVertexFan.coloredFan] using
      fan.coloredFan.canonicalColoring_third

/-- Evaluating the port coloring transported through all selected rotation
rounds at an endpoint's final port recovers that endpoint's edge color. -/
theorem ContractedVertexFan.rotateColoring_finalNormalizedPort
    {problem : PeriodicThreeDM}
    {presentation : problem.ContinuousPlanarPresentation}
    {vertex : PeriodicThreeDMVertex}
    (fan : ContractedVertexFan presentation vertex)
    (endpoint : ContractedEndpoint)
    (member : endpoint ∈ [fan.first, fan.second, fan.third]) :
    rotateColoring
        (rotationCountAt presentation.toPlanarPresentation vertex)
        (canonicalColoringAt presentation.toPlanarPresentation vertex)
        (endpoint.finalNormalizedPort presentation.toPlanarPresentation) =
      endpoint.color := by
  have endpointVertex : endpoint.vertex = vertex := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with first | second | third
    · simpa [first] using fan.first_data.2
    · simpa [second] using fan.second_data.2
    · simpa [third] using fan.third_data.2
  unfold rotateColoring
  rw [← endpointVertex]
  rw [endpoint.oldPortAfterRotations_finalNormalizedPort]
  simpa [endpointVertex] using
    fan.canonicalColoringAt_firstNormalizedPort endpoint member

/-- At a trichromatic vertex, the actual selected drawing cell exposes each
fan endpoint's edge color on that endpoint's final normalized port. -/
theorem ContractedVertexFan.finalVertexCellType_portColor_triple
    {problem : PeriodicThreeDM}
    {presentation : problem.ContinuousPlanarPresentation}
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (tripleIndex : Nat)
    (indexLt : tripleIndex < problem.triples.length)
    (fan : ContractedVertexFan presentation (.triple tripleIndex))
    (endpoint : ContractedEndpoint)
    (member : endpoint ∈ [fan.first, fan.second, fan.third]) :
    (presentation.toPlanarPresentation.finalVertexCellType
        (.triple tripleIndex)).portColor
        (endpoint.finalNormalizedPort
          presentation.toPlanarPresentation).side =
      some endpoint.color := by
  have transported :=
    fan.rotateColoring_finalNormalizedPort endpoint member
  have normalized :
      normalizeTrichromaticColoring
          (canonicalColoringAt presentation.toPlanarPresentation
            (.triple tripleIndex))
          (endpoint.finalNormalizedPort
            presentation.toPlanarPresentation) =
        endpoint.color := by
    simpa [normalizeTrichromaticColoring,
      rotationCountAt] using transported
  have ports :=
    PlanarPresentation.finalVertexCellType_portColors_triple presentation
      wellFormed degree tripleIndex indexLt
  generalize portEquation :
    endpoint.finalNormalizedPort presentation.toPlanarPresentation = port
      at normalized ⊢
  cases port <;>
    simp_all [CanonicalVertexPort.side]

/-- At a retained monochromatic element, every final canonical endpoint port
exposes the element—and hence endpoint—color. -/
theorem ContractedVertexFan.finalVertexCellType_portColor_element
    {problem : PeriodicThreeDM}
    {presentation : problem.ContinuousPlanarPresentation}
    (color : WireColor) (atom : Nat)
    (fan : ContractedVertexFan presentation (.element color atom))
    (endpoint : ContractedEndpoint)
    (member : endpoint ∈ [fan.first, fan.second, fan.third]) :
    (presentation.toPlanarPresentation.finalVertexCellType
        (.element color atom)).portColor
        (endpoint.finalNormalizedPort
          presentation.toPlanarPresentation).side =
      some endpoint.color := by
  have endpointVertex : endpoint.vertex = .element color atom := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with first | second | third
    · simpa [first] using fan.first_data.2
    · simpa [second] using fan.second_data.2
    · simpa [third] using fan.third_data.2
  have endpointColor :=
    endpoint.color_eq_of_vertex_eq_element color atom endpointVertex
  have ports :=
    PlanarPresentation.finalVertexCellType_portColors_element
      presentation.toPlanarPresentation color atom
  generalize portEquation :
    endpoint.finalNormalizedPort presentation.toPlanarPresentation = port
      at ⊢
  cases port <;>
    simp_all [CanonicalVertexPort.side]

end PeriodicThreeDM
end LeanTrominoes
