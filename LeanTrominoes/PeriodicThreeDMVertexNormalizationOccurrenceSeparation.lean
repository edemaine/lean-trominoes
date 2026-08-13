/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMVertexNormalizationTemplateCorridorOccurrenceSeparation

/-!
# Separation of complete first-round route occurrences

The source template, trimmed middle corridor, and reversed target template
are now assembled.  Pairwise source prefixes retain only head contacts,
pairwise target suffixes retain only tail contacts, and the two cross
pairings retain only the corresponding outer head--tail contact.
-/

namespace LeanTrominoes

open PeriodicOrthocrossing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
open DegreeThreeVertexNormalization

namespace PeriodicThreeDM

/-- Reversing the second of two head-contacting routes turns its common head
into the second route's tail. -/
theorem routesMeetOnlyAtFirstHeadSecondTail_reverse_right
    {first second : List Cell}
    (contacts : RoutesMeetOnlyAtHeads first second) :
    RoutesMeetOnlyAtFirstHeadSecondTail first second.reverse := by
  intro firstPoint firstMember secondPoint secondMember equal
  have originalSecondMember : secondPoint ∈ second :=
    List.mem_reverse.mp secondMember
  have heads := contacts firstPoint firstMember
    secondPoint originalSecondMember equal
  exact ⟨heads.1, by simpa [List.getLast?_reverse] using heads.2⟩

/-- Joining a strict suffix to a head--tail-contacting prefix preserves the
same outer contact classification. -/
theorem routesAvoidAndMeetOnlyAtFirstHeadSecondTail_join_left
    {first suffix second : List Cell} {middle : Cell}
    (firstAvoid : RoutesAvoidEachOther first second)
    (firstContacts : RoutesMeetOnlyAtFirstHeadSecondTail first second)
    (suffixStrict : RoutesStrictlyAvoidEachOther suffix second)
    (firstLast : first.getLast? = some middle)
    (suffixHead : suffix.head? = some middle) :
    RoutesAvoidEachOther (joinAtEndpoint first suffix) second ∧
      RoutesMeetOnlyAtFirstHeadSecondTail
        (joinAtEndpoint first suffix) second := by
  have firstHeadContacts : RoutesMeetOnlyAtFirstHead first second := by
    intro firstPoint firstMember secondPoint secondMember equal
    have outer := firstContacts firstPoint firstMember
      secondPoint secondMember equal
    exact ⟨outer.1, Or.inr outer.2⟩
  have suffixTailContacts : RoutesMeetOnlyAtFirstTail suffix second :=
    RoutesMeetOnlyAtFirstTail.of_strict suffixStrict
  refine
    ⟨firstAvoid.join_left_of_outer_endpoint_contacts
      firstHeadContacts suffixStrict.toRoutesAvoidEachOther
      suffixTailContacts firstLast suffixHead, ?_⟩
  intro joinedPoint joinedMember secondPoint secondMember equal
  rcases mem_joinAtEndpoint joinedMember with
      firstMember | suffixMember
  · have outer := firstContacts joinedPoint firstMember
      secondPoint secondMember equal
    exact ⟨joinAtEndpoint_head? outer.1, outer.2⟩
  · exact
      (suffixStrict.2.2.2 joinedPoint suffixMember
        secondPoint secondMember equal).elim

/-- Exact source-template/middle and middle/reversed-target splice
boundaries for one lifted first-round route. -/
theorem ContinuousPlanarPresentation.firstNormalizationOccurrence_junctions
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    {edge : ContractedEdge}
    (edgeMember : edge ∈ problem.contractedEdges)
    (routeTranslate : Cell) :
    let planar := presentation.toPlanarPresentation
    let sourceRoute := planar.firstNormalizationTemplateOccurrence
      (.source edge) routeTranslate
    let middleRoute := planar.firstNormalizationCorridorOccurrence
      edge routeTranslate
    let targetRoute :=
      (planar.firstNormalizationTemplateOccurrence
        (.target edge) routeTranslate).reverse
    ∃ sourceBoundary targetBoundary,
      sourceRoute.getLast? = some sourceBoundary ∧
      middleRoute.head? = some sourceBoundary ∧
      middleRoute.getLast? = some targetBoundary ∧
      targetRoute.head? = some targetBoundary := by
  dsimp only
  let planar := presentation.toPlanarPresentation
  let oldRoute :=
    planar.contractedEdgeRouteOccurrence edge routeTranslate
  let sourceEndpoint := ContractedEndpoint.source edge
  let targetEndpoint := ContractedEndpoint.target edge
  let sourcePosition := planar.contractedEndpointOccurrencePosition
    sourceEndpoint routeTranslate
  let targetPosition := planar.contractedEndpointOccurrencePosition
    targetEndpoint routeTranslate
  have sourceMember : sourceEndpoint ∈ problem.contractedEndpoints := by
    simp [sourceEndpoint, contractedEndpoints, edgeMember]
  have targetMember : targetEndpoint ∈ problem.contractedEndpoints := by
    simp [targetEndpoint, contractedEndpoints, edgeMember]
  have routeLength : 2 ≤ oldRoute.length :=
    planar.contractedEdgeRouteOccurrence_length_ge_two
      degree edgeMember routeTranslate
  have oldOrthogonal : OrthogonalPolyline oldRoute :=
    planar.contractedEdgeRouteOccurrence_orthogonal
      edgeMember routeTranslate
  obtain ⟨first, second, rest, sourceEquation⟩ :=
    List.exists_eq_cons_cons_of_length_ge_two routeLength
  obtain ⟨leading, before, last, targetEquation⟩ :=
    AxisDirection.exists_eq_append_pair_of_length_ge_two routeLength
  have endpoints :=
    planar.contractedEdgeRouteOccurrence_normalizationEndpoints
      edgeMember routeTranslate
  change oldRoute.head? = some sourcePosition ∧
    oldRoute.getLast? = some targetPosition at endpoints
  have firstEqual : first = sourcePosition := by
    rw [sourceEquation] at endpoints
    exact Option.some.inj endpoints.1
  have lastEqual : last = targetPosition := by
    rw [targetEquation] at endpoints
    apply Option.some.inj
    simpa using endpoints.2
  subst first
  subst last
  have sourceAligned :
      (GridSegment.mk sourcePosition second).IsAxisAligned := by
    rw [sourceEquation] at oldOrthogonal
    exact (List.isChain_cons_cons.mp oldOrthogonal).1
  have targetAligned :
      (GridSegment.mk before targetPosition).IsAxisAligned := by
    rw [targetEquation] at oldOrthogonal
    exact (List.isChain_append_cons_cons.mp oldOrthogonal).2.1
  have sourceDirection :
      AxisDirection.between sourcePosition second =
        (sourceEndpoint.outwardSide planar).direction := by
    calc
      _ = AxisDirection.polylineFirstDirection oldRoute := by
        rw [sourceEquation]
        rfl
      _ = AxisDirection.polylineFirstDirection
          (planar.contractedEdgeRoute edge) := by
        simp [oldRoute, PlanarPresentation.contractedEdgeRouteOccurrence]
      _ = sourceEndpoint.outwardDirection planar := by rfl
      _ = (sourceEndpoint.outwardSide planar).direction :=
        (sourceEndpoint.outwardSide_direction
          planar degree sourceMember).symm
  have targetDirection :
      AxisDirection.between targetPosition before =
        (targetEndpoint.outwardSide planar).direction := by
    calc
      _ = (AxisDirection.polylineLastDirection oldRoute).opposite := by
        rw [targetEquation]
        rw [AxisDirection.polylineLastDirection_append_pair_of_axisAligned
          leading targetAligned]
        exact AxisDirection.between_reverse_eq_opposite
          (AxisDirection.between_isGenuine_of_axisAligned targetAligned)
      _ = (AxisDirection.polylineLastDirection
          (planar.contractedEdgeRoute edge)).opposite := by
        simp [oldRoute, PlanarPresentation.contractedEdgeRouteOccurrence]
      _ = targetEndpoint.outwardDirection planar := by rfl
      _ = (targetEndpoint.outwardSide planar).direction :=
        (targetEndpoint.outwardSide_direction
          planar degree targetMember).symm
  have sourceUsed := sourceEndpoint.outwardSide_ne_omittedSideAt
    presentation wellFormed degree sourceMember
  have targetUsed := targetEndpoint.outwardSide_ne_omittedSideAt
    presentation wellFormed degree targetMember
  let sourceBoundary := Cell.add (normalizeVertexPosition sourcePosition)
    (Cell.scale 3 (sourceEndpoint.outwardSide planar).direction.step)
  let targetBoundary := Cell.add (normalizeVertexPosition targetPosition)
    (Cell.scale 3 (targetEndpoint.outwardSide planar).direction.step)
  refine ⟨sourceBoundary, targetBoundary, ?_, ?_, ?_, ?_⟩
  · unfold PlanarPresentation.firstNormalizationTemplateOccurrence
      sourceBoundary
    exact normalizationTemplateAt_getLast?_of_three_steps
      sourcePosition
      (sourceEndpoint.firstNormalizationTemplate_getLast?
        planar sourceUsed)
  · unfold PlanarPresentation.firstNormalizationCorridorOccurrence
      sourceBoundary
    rw [← sourceDirection]
    exact trimmedMagnifiedRoute_head?_of_endpoints
      oldRoute endpoints.1 (by simp [sourceEquation]) sourceAligned
  · unfold PlanarPresentation.firstNormalizationCorridorOccurrence
      targetBoundary
    rw [← targetDirection]
    exact trimmedMagnifiedRoute_getLast?_of_endpoints
      oldRoute endpoints.2 (by simp [targetEquation]) targetAligned
  · unfold PlanarPresentation.firstNormalizationTemplateOccurrence
      targetBoundary
    simp only [List.head?_reverse]
    exact normalizationTemplateAt_getLast?_of_three_steps
      targetPosition
      (targetEndpoint.firstNormalizationTemplate_getLast?
        planar targetUsed)

/-- Two distinct contracted edge occurrences remain completely separated
after the first vertex-normalization splice. -/
theorem ContinuousPlanarPresentation.normalizationRouteOccurrences1_avoidEachOther
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
    RoutesAvoidEachOther
      (planar.normalizationRouteOccurrence1 firstEdge firstTranslate)
      (planar.normalizationRouteOccurrence1 secondEdge secondTranslate) := by
  dsimp only
  let planar := presentation.toPlanarPresentation
  let firstSourceEndpoint := ContractedEndpoint.source firstEdge
  let firstTargetEndpoint := ContractedEndpoint.target firstEdge
  let secondSourceEndpoint := ContractedEndpoint.source secondEdge
  let secondTargetEndpoint := ContractedEndpoint.target secondEdge
  let firstSource := planar.firstNormalizationTemplateOccurrence
    firstSourceEndpoint firstTranslate
  let firstMiddle := planar.firstNormalizationCorridorOccurrence
    firstEdge firstTranslate
  let firstTarget :=
    (planar.firstNormalizationTemplateOccurrence
      firstTargetEndpoint firstTranslate).reverse
  let secondSource := planar.firstNormalizationTemplateOccurrence
    secondSourceEndpoint secondTranslate
  let secondMiddle := planar.firstNormalizationCorridorOccurrence
    secondEdge secondTranslate
  let secondTarget :=
    (planar.firstNormalizationTemplateOccurrence
      secondTargetEndpoint secondTranslate).reverse
  have firstSourceMember :
      firstSourceEndpoint ∈ problem.contractedEndpoints := by
    simp [firstSourceEndpoint, contractedEndpoints, firstMember]
  have firstTargetMember :
      firstTargetEndpoint ∈ problem.contractedEndpoints := by
    simp [firstTargetEndpoint, contractedEndpoints, firstMember]
  have secondSourceMember :
      secondSourceEndpoint ∈ problem.contractedEndpoints := by
    simp [secondSourceEndpoint, contractedEndpoints, secondMember]
  have secondTargetMember :
      secondTargetEndpoint ∈ problem.contractedEndpoints := by
    simp [secondTargetEndpoint, contractedEndpoints, secondMember]
  have sourceOccurrencesDifferent :
      (firstSourceEndpoint, firstTranslate) ≠
        (secondSourceEndpoint, secondTranslate) := by
    intro equal
    have endpointsEqual := congrArg Prod.fst equal
    have translatesEqual := congrArg Prod.snd equal
    have edgesEqual : firstEdge = secondEdge := by
      injection endpointsEqual
    exact different (Prod.ext edgesEqual translatesEqual)
  have targetOccurrencesDifferent :
      (firstTargetEndpoint, firstTranslate) ≠
        (secondTargetEndpoint, secondTranslate) := by
    intro equal
    have endpointsEqual := congrArg Prod.fst equal
    have translatesEqual := congrArg Prod.snd equal
    have edgesEqual : firstEdge = secondEdge := by
      injection endpointsEqual
    exact different (Prod.ext edgesEqual translatesEqual)
  have firstSourceSecondTargetDifferent :
      (firstSourceEndpoint, firstTranslate) ≠
        (secondTargetEndpoint, secondTranslate) := by
    intro equal
    have endpointsEqual := congrArg Prod.fst equal
    cases endpointsEqual
  have secondSourceFirstTargetDifferent :
      (secondSourceEndpoint, secondTranslate) ≠
        (firstTargetEndpoint, firstTranslate) := by
    intro equal
    have endpointsEqual := congrArg Prod.fst equal
    cases endpointsEqual
  rcases presentation.firstNormalizationOccurrence_junctions
      wellFormed degree firstMember firstTranslate with
    ⟨firstSourceBoundary, firstTargetBoundary,
      firstSourceLast, firstMiddleHead,
      firstMiddleLast, firstTargetHead⟩
  rcases presentation.firstNormalizationOccurrence_junctions
      wellFormed degree secondMember secondTranslate with
    ⟨secondSourceBoundary, secondTargetBoundary,
      secondSourceLast, secondMiddleHead,
      secondMiddleLast, secondTargetHead⟩
  have sourcePair :=
    presentation.firstNormalizationTemplateOccurrences_avoid
      wellFormed degree firstSourceMember secondSourceMember
      sourceOccurrencesDifferent
  have firstSourceSecondMiddle :
      RoutesStrictlyAvoidEachOther firstSource secondMiddle := by
    exact
      presentation.firstNormalizationTemplateOccurrence_strictlyAvoids_corridorOccurrence
        wellFormed degree separated sourceSimple
        firstSourceMember secondMember different
  have firstMiddleSecondSource :
      RoutesStrictlyAvoidEachOther firstMiddle secondSource := by
    exact
      presentation.firstNormalizationCorridorOccurrence_strictlyAvoids_templateOccurrence
        wellFormed degree separated sourceSimple
        secondSourceMember firstMember different.symm
  have middlesStrict :
      RoutesStrictlyAvoidEachOther firstMiddle secondMiddle := by
    exact planar.firstNormalizationCorridorOccurrences_strictlyAvoid
      degree separated sourceSimple firstMember secondMember
      firstTranslate secondTranslate different
  have prefixes :=
    sourcePair.1.join_tails_of_prefixes_meet_only_at_heads
      sourcePair.2 firstSourceSecondMiddle firstMiddleSecondSource
      middlesStrict
      firstSourceLast firstMiddleHead
      secondSourceLast secondMiddleHead
  have targetPair :=
    presentation.reversedFirstNormalizationTemplateOccurrences_avoid
      wellFormed degree firstTargetMember secondTargetMember
      targetOccurrencesDifferent
  have firstSourceSecondTargetPair :=
    presentation.firstNormalizationTemplateOccurrences_avoid
      wellFormed degree firstSourceMember secondTargetMember
      firstSourceSecondTargetDifferent
  have firstSourceSecondTargetAvoid :
      RoutesAvoidEachOther firstSource secondTarget :=
    firstSourceSecondTargetPair.1.reverse_right
  have firstSourceSecondTargetContacts :
      RoutesMeetOnlyAtFirstHeadSecondTail firstSource secondTarget :=
    routesMeetOnlyAtFirstHeadSecondTail_reverse_right
      firstSourceSecondTargetPair.2
  have firstMiddleSecondTargetStrict :
      RoutesStrictlyAvoidEachOther firstMiddle secondTarget := by
    have forward :=
      presentation.firstNormalizationCorridorOccurrence_strictlyAvoids_templateOccurrence
        wellFormed degree separated sourceSimple
        secondTargetMember firstMember different.symm
    exact forward.reverse_right
  have firstPrefixSecondTarget :=
    routesAvoidAndMeetOnlyAtFirstHeadSecondTail_join_left
      firstSourceSecondTargetAvoid
      firstSourceSecondTargetContacts
      firstMiddleSecondTargetStrict
      firstSourceLast firstMiddleHead
  have secondSourceFirstTargetPair :=
    presentation.firstNormalizationTemplateOccurrences_avoid
      wellFormed degree secondSourceMember firstTargetMember
      secondSourceFirstTargetDifferent
  have secondSourceFirstTargetAvoid :
      RoutesAvoidEachOther secondSource firstTarget :=
    secondSourceFirstTargetPair.1.reverse_right
  have secondSourceFirstTargetContacts :
      RoutesMeetOnlyAtFirstHeadSecondTail secondSource firstTarget :=
    routesMeetOnlyAtFirstHeadSecondTail_reverse_right
      secondSourceFirstTargetPair.2
  have secondMiddleFirstTargetStrict :
      RoutesStrictlyAvoidEachOther secondMiddle firstTarget := by
    have forward :=
      presentation.firstNormalizationCorridorOccurrence_strictlyAvoids_templateOccurrence
        wellFormed degree separated sourceSimple
        firstTargetMember secondMember different
    exact forward.reverse_right
  have secondPrefixFirstTarget :=
    routesAvoidAndMeetOnlyAtFirstHeadSecondTail_join_left
      secondSourceFirstTargetAvoid
      secondSourceFirstTargetContacts
      secondMiddleFirstTargetStrict
      secondSourceLast secondMiddleHead
  have firstPrefixLast :
      (joinAtEndpoint firstSource firstMiddle).getLast? =
        some firstTargetBoundary :=
    joinAtEndpoint_getLast?
      firstSourceLast firstMiddleHead firstMiddleLast
  have secondPrefixLast :
      (joinAtEndpoint secondSource secondMiddle).getLast? =
        some secondTargetBoundary :=
    joinAtEndpoint_getLast?
      secondSourceLast secondMiddleHead secondMiddleLast
  have assembled : RoutesAvoidEachOther
      (joinAtEndpoint (joinAtEndpoint firstSource firstMiddle) firstTarget)
      (joinAtEndpoint (joinAtEndpoint secondSource secondMiddle) secondTarget) :=
    prefixes.1.join_both_of_outer_endpoint_contacts
      prefixes.2
      firstPrefixSecondTarget.1 firstPrefixSecondTarget.2
      (routesAvoidEachOther_comm secondPrefixFirstTarget.1)
      secondPrefixFirstTarget.2
      targetPair.1 targetPair.2
      firstPrefixLast firstTargetHead
      secondPrefixLast secondTargetHead
  have firstMiddleNe : firstMiddle ≠ [] := by
    exact List.ne_nil_of_mem
      (List.mem_of_mem_head? firstMiddleHead)
  have secondMiddleNe : secondMiddle ≠ [] := by
    exact List.ne_nil_of_mem
      (List.mem_of_mem_head? secondMiddleHead)
  rw [planar.normalizationRouteOccurrence1_eq_threePieces,
    planar.normalizationRouteOccurrence1_eq_threePieces,
    joinAtEndpoint_assoc_of_middle_ne_nil firstMiddleNe,
    joinAtEndpoint_assoc_of_middle_ne_nil secondMiddleNe]
  exact assembled

end PeriodicThreeDM
end LeanTrominoes
