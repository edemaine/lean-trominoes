import LeanTrominoes.PeriodicThreeDMVertexNormalizationCyclicTemplateCorridorOccurrenceSeparation

/-!
# Separation of complete first cyclic-round route occurrences

The source cyclic template, trimmed middle corridor, and reversed target
template are assembled using their exact junctions.  Pairwise separation of
all nine piece combinations then yields complete separation of distinct
second-round route occurrences.
-/

namespace LeanTrominoes

open PeriodicOrthocrossing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
open DegreeThreeVertexNormalization

namespace PeriodicThreeDM

/-- Reversing both cyclic target templates turns their possible common head
into a tail-to-tail contact. -/
theorem ContinuousPlanarPresentation.reversedSecondNormalizationTemplateOccurrences_avoid
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
          first firstTranslate).reverse
        (planar.secondNormalizationTemplateOccurrence
          second secondTranslate).reverse ∧
      RoutesMeetOnlyAtTails
        (planar.secondNormalizationTemplateOccurrence
          first firstTranslate).reverse
        (planar.secondNormalizationTemplateOccurrence
          second secondTranslate).reverse := by
  dsimp only
  have forward :=
    presentation.secondNormalizationTemplateOccurrences_avoid
      wellFormed degree firstMember secondMember different
  exact ⟨routesAvoidEachOther_reverse forward.1,
    routesMeetOnlyAtTails_reverse forward.2⟩

/-- Exact source-template/middle and middle/reversed-target splice
boundaries for one lifted first cyclic-round route. -/
theorem ContinuousPlanarPresentation.secondNormalizationOccurrence_junctions
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    {edge : ContractedEdge}
    (edgeMember : edge ∈ problem.contractedEdges)
    (routeTranslate : Cell) :
    let planar := presentation.toPlanarPresentation
    let sourceRoute := planar.secondNormalizationTemplateOccurrence
      (.source edge) routeTranslate
    let middleRoute := planar.secondNormalizationCorridorOccurrence
      edge routeTranslate
    let targetRoute :=
      (planar.secondNormalizationTemplateOccurrence
        (.target edge) routeTranslate).reverse
    ∃ sourceBoundary targetBoundary,
      sourceRoute.getLast? = some sourceBoundary ∧
      middleRoute.head? = some sourceBoundary ∧
      middleRoute.getLast? = some targetBoundary ∧
      targetRoute.head? = some targetBoundary := by
  dsimp only
  let planar := presentation.toPlanarPresentation
  let oldRoute := planar.normalizationRouteOccurrence1 edge routeTranslate
  let sourceEndpoint := ContractedEndpoint.source edge
  let targetEndpoint := ContractedEndpoint.target edge
  let sourcePosition := planar.normalizationEndpointOccurrencePosition1
    sourceEndpoint routeTranslate
  let targetPosition := planar.normalizationEndpointOccurrencePosition1
    targetEndpoint routeTranslate
  let sourcePort := sourceEndpoint.firstNormalizedPort planar
  let targetPort := targetEndpoint.firstNormalizedPort planar
  have routeLength : 2 ≤ oldRoute.length :=
    presentation.normalizationRouteOccurrence1_length_ge_two
      degree edgeMember routeTranslate
  have oldOrthogonal : OrthogonalPolyline oldRoute :=
    (presentation.normalizationRouteOccurrence1_unitSteps
      wellFormed degree edgeMember routeTranslate).imp
        (fun _ _ step => step.isAxisAligned)
  obtain ⟨first, second, rest, sourceEquation⟩ :=
    List.exists_eq_cons_cons_of_length_ge_two routeLength
  obtain ⟨leading, before, last, targetEquation⟩ :=
    AxisDirection.exists_eq_append_pair_of_length_ge_two routeLength
  have geometry :=
    presentation.normalizationRouteOccurrence1_endpointGeometry
      degree edgeMember routeTranslate
  change oldRoute.head? = some sourcePosition ∧
    oldRoute.tail.head? = some
      (Cell.add sourcePosition sourcePort.direction.step) ∧
    oldRoute.getLast? = some targetPosition ∧
    oldRoute.reverse.tail.head? = some
      (Cell.add targetPosition targetPort.direction.step) at geometry
  have firstEqual : first = sourcePosition := by
    rw [sourceEquation] at geometry
    exact Option.some.inj geometry.1
  have secondEqual : second =
      Cell.add sourcePosition sourcePort.direction.step := by
    rw [sourceEquation] at geometry
    exact Option.some.inj geometry.2.1
  have lastEqual : last = targetPosition := by
    rw [targetEquation] at geometry
    apply Option.some.inj
    simpa using geometry.2.2.1
  have beforeEqual : before =
      Cell.add targetPosition targetPort.direction.step := by
    rw [targetEquation] at geometry
    apply Option.some.inj
    simpa using geometry.2.2.2
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
      AxisDirection.between sourcePosition second = sourcePort.direction := by
    rw [secondEqual]
    exact AxisDirection.between_add_step _
      (CanonicalVertexPort.direction_isGenuine sourcePort)
  have targetDirection :
      AxisDirection.between targetPosition before = targetPort.direction := by
    rw [beforeEqual]
    exact AxisDirection.between_add_step _
      (CanonicalVertexPort.direction_isGenuine targetPort)
  let sourceBoundary := Cell.add (normalizeVertexPosition sourcePosition)
    (Cell.scale 3 sourcePort.direction.step)
  let targetBoundary := Cell.add (normalizeVertexPosition targetPosition)
    (Cell.scale 3 targetPort.direction.step)
  refine ⟨sourceBoundary, targetBoundary, ?_, ?_, ?_, ?_⟩
  · unfold PlanarPresentation.secondNormalizationTemplateOccurrence
      sourceBoundary
    exact normalizationTemplateAt_getLast?_of_three_steps
      sourcePosition
      (sourceEndpoint.secondNormalizationTemplate_getLast? planar)
  · unfold PlanarPresentation.secondNormalizationCorridorOccurrence
      sourceBoundary
    rw [← sourceDirection]
    exact trimmedMagnifiedRoute_head?_of_endpoints
      oldRoute geometry.1 (by simp [sourceEquation]) sourceAligned
  · unfold PlanarPresentation.secondNormalizationCorridorOccurrence
      targetBoundary
    rw [← targetDirection]
    exact trimmedMagnifiedRoute_getLast?_of_endpoints
      oldRoute geometry.2.2.1 (by simp [targetEquation]) targetAligned
  · unfold PlanarPresentation.secondNormalizationTemplateOccurrence
      targetBoundary
    simp only [List.head?_reverse]
    exact normalizationTemplateAt_getLast?_of_three_steps
      targetPosition
      (targetEndpoint.secondNormalizationTemplate_getLast? planar)

/-- Two distinct contracted edge occurrences remain completely separated
after the first cyclic normalization splice. -/
theorem ContinuousPlanarPresentation.normalizationRouteOccurrences2_avoidEachOther
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
      (planar.normalizationRouteOccurrence2 firstEdge firstTranslate)
      (planar.normalizationRouteOccurrence2 secondEdge secondTranslate) := by
  dsimp only
  let planar := presentation.toPlanarPresentation
  let firstSourceEndpoint := ContractedEndpoint.source firstEdge
  let firstTargetEndpoint := ContractedEndpoint.target firstEdge
  let secondSourceEndpoint := ContractedEndpoint.source secondEdge
  let secondTargetEndpoint := ContractedEndpoint.target secondEdge
  let firstSource := planar.secondNormalizationTemplateOccurrence
    firstSourceEndpoint firstTranslate
  let firstMiddle := planar.secondNormalizationCorridorOccurrence
    firstEdge firstTranslate
  let firstTarget :=
    (planar.secondNormalizationTemplateOccurrence
      firstTargetEndpoint firstTranslate).reverse
  let secondSource := planar.secondNormalizationTemplateOccurrence
    secondSourceEndpoint secondTranslate
  let secondMiddle := planar.secondNormalizationCorridorOccurrence
    secondEdge secondTranslate
  let secondTarget :=
    (planar.secondNormalizationTemplateOccurrence
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
  rcases presentation.secondNormalizationOccurrence_junctions
      wellFormed degree firstMember firstTranslate with
    ⟨firstSourceBoundary, firstTargetBoundary,
      firstSourceLast, firstMiddleHead,
      firstMiddleLast, firstTargetHead⟩
  rcases presentation.secondNormalizationOccurrence_junctions
      wellFormed degree secondMember secondTranslate with
    ⟨secondSourceBoundary, secondTargetBoundary,
      secondSourceLast, secondMiddleHead,
      secondMiddleLast, secondTargetHead⟩
  have sourcePair :=
    presentation.secondNormalizationTemplateOccurrences_avoid
      wellFormed degree firstSourceMember secondSourceMember
      sourceOccurrencesDifferent
  have firstSourceSecondMiddle :
      RoutesStrictlyAvoidEachOther firstSource secondMiddle := by
    exact
      presentation.secondNormalizationTemplateOccurrence_strictlyAvoids_corridorOccurrence
        wellFormed degree separated sourceSimple
        firstSourceMember secondMember different
  have firstMiddleSecondSource :
      RoutesStrictlyAvoidEachOther firstMiddle secondSource := by
    exact
      presentation.secondNormalizationCorridorOccurrence_strictlyAvoids_templateOccurrence
        wellFormed degree separated sourceSimple
        secondSourceMember firstMember different.symm
  have middlesStrict :
      RoutesStrictlyAvoidEachOther firstMiddle secondMiddle := by
    exact presentation.secondNormalizationCorridorOccurrences_strictlyAvoid
      wellFormed degree separated sourceSimple firstMember secondMember
      firstTranslate secondTranslate different
  have prefixes :=
    sourcePair.1.join_tails_of_prefixes_meet_only_at_heads
      sourcePair.2 firstSourceSecondMiddle firstMiddleSecondSource
      middlesStrict
      firstSourceLast firstMiddleHead
      secondSourceLast secondMiddleHead
  have targetPair :=
    presentation.reversedSecondNormalizationTemplateOccurrences_avoid
      wellFormed degree firstTargetMember secondTargetMember
      targetOccurrencesDifferent
  have firstSourceSecondTargetPair :=
    presentation.secondNormalizationTemplateOccurrences_avoid
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
      presentation.secondNormalizationCorridorOccurrence_strictlyAvoids_templateOccurrence
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
    presentation.secondNormalizationTemplateOccurrences_avoid
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
      presentation.secondNormalizationCorridorOccurrence_strictlyAvoids_templateOccurrence
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
  rw [planar.normalizationRouteOccurrence2_eq_threePieces,
    planar.normalizationRouteOccurrence2_eq_threePieces,
    joinAtEndpoint_assoc_of_middle_ne_nil firstMiddleNe,
    joinAtEndpoint_assoc_of_middle_ne_nil secondMiddleNe]
  exact assembled

end PeriodicThreeDM
end LeanTrominoes
