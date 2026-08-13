/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMVertexNormalizationCyclicTemplateSeparation

/-!
# Lifted corridors for the first cyclic normalization round

The first intermediate drawing already has complete lifted separation and
simple unit-step routes.  Scaling, subdividing, and symmetrically trimming
two distinct lifted occurrences therefore makes their second-round middle
corridors strictly disjoint.
-/

namespace LeanTrominoes

open PeriodicOrthocrossing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

namespace PeriodicThreeDM

/-- Translation preserves the simplicity of every first-round normalized
route occurrence. -/
theorem ContinuousPlanarPresentation.normalizationRouteOccurrence1_isSimple
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (separated : presentation.drawing.LiftedRoutesAvoidEachOther)
    (sourceSimple :
      ∀ route ∈ presentation.drawing.edgeRoutes,
        LocalIncidenceDrawing.RouteIsSimple route)
    {edge : ContractedEdge}
    (edgeMember : edge ∈ problem.contractedEdges)
    (routeTranslate : Cell) :
    LocalIncidenceDrawing.RouteIsSimple
      (presentation.toPlanarPresentation
        |>.normalizationRouteOccurrence1 edge routeTranslate) := by
  let planar := presentation.toPlanarPresentation
  unfold PlanarPresentation.normalizationRouteOccurrence1
    PeriodicOrthocrossing.translatePolyline
  exact routeIsSimple_translate
    (presentation.normalizationRoute1_isSimple
      wellFormed degree separated sourceSimple edgeMember)
    (planar.normalizationGridDrawing1.periodTranslation routeTranslate)

/-- Every lifted first-round normalized route remains a unit-step chain. -/
theorem ContinuousPlanarPresentation.normalizationRouteOccurrence1_unitSteps
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    {edge : ContractedEdge}
    (edgeMember : edge ∈ problem.contractedEdges)
    (routeTranslate : Cell) :
    (presentation.toPlanarPresentation
      |>.normalizationRouteOccurrence1 edge routeTranslate)
      |>.IsChain AxisDirection.IsUnitAxisStep := by
  let planar := presentation.toPlanarPresentation
  unfold PlanarPresentation.normalizationRouteOccurrence1
    PeriodicOrthocrossing.translatePolyline
  apply List.isChain_map_of_isChain
    (Cell.add
      (planar.normalizationGridDrawing1.periodTranslation routeTranslate))
  · intro first second step
    exact AxisDirection.IsUnitAxisStep.translate step _
  · exact presentation.normalizationRoute1_unitSteps
      wellFormed degree edgeMember

/-- Every lifted first-round normalized route has at least two points. -/
theorem ContinuousPlanarPresentation.normalizationRouteOccurrence1_length_ge_two
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (degree : problem.DegreeTwoOrThree)
    {edge : ContractedEdge}
    (edgeMember : edge ∈ problem.contractedEdges)
    (routeTranslate : Cell) :
    2 ≤ (presentation.toPlanarPresentation
      |>.normalizationRouteOccurrence1 edge routeTranslate).length := by
  have endpoints := presentation.normalizationRoute1_endpointGeometry
    degree edgeMember
  have baseLength : 2 ≤
      (presentation.toPlanarPresentation.normalizationRoute1 edge).length :=
    List.two_le_length_of_tail_head?_eq_some endpoints.2.1
  simpa [PlanarPresentation.normalizationRouteOccurrence1,
    PeriodicOrthocrossing.translatePolyline] using baseLength

/-- Two distinct first-round route occurrences yield strictly separated
second-round middle corridors. -/
theorem ContinuousPlanarPresentation.secondNormalizationCorridorOccurrences_strictlyAvoid
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (separated : presentation.drawing.LiftedRoutesAvoidEachOther)
    (sourceSimple :
      ∀ route ∈ presentation.drawing.edgeRoutes,
        LocalIncidenceDrawing.RouteIsSimple route)
    {firstEdge secondEdge : ContractedEdge}
    (firstMember : firstEdge ∈ problem.contractedEdges)
    (secondMember : secondEdge ∈ problem.contractedEdges)
    (firstTranslate secondTranslate : Cell)
    (different : (firstEdge, firstTranslate) ≠
      (secondEdge, secondTranslate)) :
    let planar := presentation.toPlanarPresentation
    RoutesStrictlyAvoidEachOther
      (planar.secondNormalizationCorridorOccurrence
        firstEdge firstTranslate)
      (planar.secondNormalizationCorridorOccurrence
        secondEdge secondTranslate) := by
  dsimp only
  let planar := presentation.toPlanarPresentation
  let firstRoute := planar.normalizationRouteOccurrence1
    firstEdge firstTranslate
  let secondRoute := planar.normalizationRouteOccurrence1
    secondEdge secondTranslate
  have avoid : RoutesAvoidEachOther firstRoute secondRoute :=
    presentation.normalizationRouteOccurrences1_avoidEachOther
      wellFormed degree separated sourceSimple
      firstMember secondMember firstTranslate secondTranslate different
  have firstLength : 2 ≤ firstRoute.length :=
    presentation.normalizationRouteOccurrence1_length_ge_two
      degree firstMember firstTranslate
  have secondLength : 2 ≤ secondRoute.length :=
    presentation.normalizationRouteOccurrence1_length_ge_two
      degree secondMember secondTranslate
  have firstUnitSteps : firstRoute.IsChain
      AxisDirection.IsUnitAxisStep :=
    presentation.normalizationRouteOccurrence1_unitSteps
      wellFormed degree firstMember firstTranslate
  have secondUnitSteps : secondRoute.IsChain
      AxisDirection.IsUnitAxisStep :=
    presentation.normalizationRouteOccurrence1_unitSteps
      wellFormed degree secondMember secondTranslate
  have firstOrthogonal : OrthogonalPolyline firstRoute :=
    firstUnitSteps.imp fun _ _ step => step.isAxisAligned
  have secondOrthogonal : OrthogonalPolyline secondRoute :=
    secondUnitSteps.imp fun _ _ step => step.isAxisAligned
  have firstSimple : LocalIncidenceDrawing.RouteIsSimple firstRoute :=
    presentation.normalizationRouteOccurrence1_isSimple
      wellFormed degree separated sourceSimple
      firstMember firstTranslate
  have secondSimple : LocalIncidenceDrawing.RouteIsSimple secondRoute :=
    presentation.normalizationRouteOccurrence1_isSimple
      wellFormed degree separated sourceSimple
      secondMember secondTranslate
  have magnifiedAvoid := magnifiedUnitRoutes_avoidEachOther
    avoid firstLength secondLength firstOrthogonal secondOrthogonal
    firstSimple secondSimple
  have firstNodup := magnifiedUnitRoute_nodup
    firstOrthogonal firstSimple
  have secondNodup := magnifiedUnitRoute_nodup
    secondOrthogonal secondSimple
  have firstLong := magnifiedUnitRoute_length_ge_thirteen
    firstLength firstOrthogonal
  have secondLong := magnifiedUnitRoute_length_ge_thirteen
    secondLength secondOrthogonal
  change RoutesStrictlyAvoidEachOther
    ((magnifiedUnitRoute firstRoute).drop 3 |>.take
      ((magnifiedUnitRoute firstRoute).length - 6))
    ((magnifiedUnitRoute secondRoute).drop 3 |>.take
      ((magnifiedUnitRoute secondRoute).length - 6))
  exact symmetricTrims_strictlyAvoidEachOther
    magnifiedAvoid firstNodup secondNodup
    (by omega) (by omega)

end PeriodicThreeDM
end LeanTrominoes
