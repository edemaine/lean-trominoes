/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalPolylineTailEndpointContactSeparation
import LeanTrominoes.OrthogonalPolylineJoinSimplicity
import LeanTrominoes.PeriodicGridDrawingLiftedRouteSeparation
import LeanTrominoes.PeriodicThreeDMContractionContinuousPlanarity
import LeanTrominoes.PositionedPeriodicCNFIncidenceRouteLookup

/-!
# Endpoint contacts after degree-two contraction

Degree-two contraction concatenates two incidence routes at the suppressed
colored-element occurrence.  This module transports complete lifted-route
separation through that concatenation.  The key combinatorial fact is that
the incidence tags stored by contracted edges form a duplicate-free
partition: if a suppressed splice could be shared by two contracted route
occurrences, those occurrences were already the same.
-/

namespace LeanTrominoes

open Gadget PeriodicOrthocrossing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

namespace PeriodicGridDrawing

/-- Fundamental representatives and their lattice translations give a
unique point occurrence in the infinite periodic lift. -/
theorem fundamentalPointOccurrence_injective
    (drawing : PeriodicGridDrawing)
    {first second firstTranslate secondTranslate : Cell}
    (firstBounds : drawing.PositionInFundamentalSquare first)
    (secondBounds : drawing.PositionInFundamentalSquare second)
    (equal :
      Cell.add first (drawing.periodTranslation firstTranslate) =
        Cell.add second (drawing.periodTranslation secondTranslate)) :
    first = second ∧ firstTranslate = secondTranslate := by
  have relativeEqual :
      first = Cell.add second
        (drawing.periodTranslation
          (Cell.sub secondTranslate firstTranslate)) := by
    rcases first with ⟨firstX, firstY⟩
    rcases second with ⟨secondX, secondY⟩
    rcases firstTranslate with ⟨firstTranslateX, firstTranslateY⟩
    rcases secondTranslate with ⟨secondTranslateX, secondTranslateY⟩
    simp only [Cell.add, Cell.sub, periodTranslation, Cell.scale,
      Prod.mk.injEq] at equal ⊢
    constructor
    · rw [mul_sub]
      omega
    · rw [mul_sub]
      omega
  have pointsEqual : first = second := by
    by_contra pointsDifferent
    exact
      PositionedPeriodicCNF.fundamentalPosition_ne_translated
        drawing firstBounds secondBounds pointsDifferent relativeEqual
  subst second
  have periodPositive : (0 : Int) < drawing.gridSize := by
    exact_mod_cast Nat.zero_lt_succ drawing.gridSizePred
  have periodNonzero : (drawing.gridSize : Int) ≠ 0 :=
    ne_of_gt periodPositive
  rcases first with ⟨firstX, firstY⟩
  rcases firstTranslate with ⟨firstTranslateX, firstTranslateY⟩
  rcases secondTranslate with ⟨secondTranslateX, secondTranslateY⟩
  simp only [Cell.add, periodTranslation, Cell.scale,
    Prod.mk.injEq] at equal ⊢
  constructor
  · trivial
  · constructor
    · apply mul_left_cancel₀ periodNonzero
      omega
    · apply mul_left_cancel₀ periodNonzero
      omega

end PeriodicGridDrawing

namespace PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Reversing just the first traversal order preserves complete route
separation. -/
theorem RoutesAvoidEachOther.reverse_left
    {first second : List Cell}
    (avoid : RoutesAvoidEachOther first second) :
    RoutesAvoidEachOther first.reverse second := by
  apply routesAvoidEachOther_of_mem
  · intro firstSegment firstSegmentMember
      secondSegment secondSegmentMember
    rw [gridPolylineSegments_reverse] at firstSegmentMember
    rcases List.mem_map.mp firstSegmentMember with
      ⟨originalFirst, originalFirstMember, rfl⟩
    have originalFirstMember' :
        originalFirst ∈ gridPolylineSegments first := by
      simpa using originalFirstMember
    intro meet
    exact
      (avoid.segmentsAvoid_of_mem
        originalFirst originalFirstMember'
        secondSegment secondSegmentMember)
        ((GridSegment.interiorsMeet_reverse_left_iff
          originalFirst secondSegment).mp meet)
  · intro firstPoint firstPointMember
      secondSegment secondSegmentMember
    exact avoid.firstPointsAvoid_of_mem firstPoint
      (List.mem_reverse.mp firstPointMember)
      secondSegment secondSegmentMember
  · intro secondPoint secondPointMember
      firstSegment firstSegmentMember
    rw [gridPolylineSegments_reverse] at firstSegmentMember
    rcases List.mem_map.mp firstSegmentMember with
      ⟨originalFirst, originalFirstMember, rfl⟩
    have originalFirstMember' :
        originalFirst ∈ gridPolylineSegments first := by
      simpa using originalFirstMember
    intro contains
    exact
      (avoid.secondPointsAvoid_of_mem secondPoint secondPointMember
        originalFirst originalFirstMember')
        ((GridSegment.interiorContains_reverse
          originalFirst secondPoint).mp contains)
  · intro firstPoint firstPointMember secondPoint secondPointMember equal
    have firstOriginalMember : firstPoint ∈ first :=
      List.mem_reverse.mp firstPointMember
    rcases List.mem_iff_get.mp firstOriginalMember with
      ⟨firstIndex, firstIndexed⟩
    rcases List.mem_iff_get.mp secondPointMember with
      ⟨secondIndex, secondIndexed⟩
    have endpoints := avoid.2.2.2 firstIndex secondIndex
      (firstIndexed.trans (equal.trans secondIndexed.symm))
    rw [firstIndexed, secondIndexed] at endpoints
    exact
      ⟨(routePointIsEndpoint_reverse_iff first firstPoint).2 endpoints.1,
        endpoints.2⟩

/-- Reversing just the second traversal order also preserves complete route
separation. -/
theorem RoutesAvoidEachOther.reverse_right
    {first second : List Cell}
    (avoid : RoutesAvoidEachOther first second) :
    RoutesAvoidEachOther first second.reverse :=
  routesAvoidEachOther_comm
    ((routesAvoidEachOther_comm avoid).reverse_left)

/-- Strict separation is independently invariant under reversal of the
first route. -/
theorem RoutesStrictlyAvoidEachOther.reverse_left
    {first second : List Cell}
    (strict : RoutesStrictlyAvoidEachOther first second) :
    RoutesStrictlyAvoidEachOther first.reverse second := by
  apply routesStrictlyAvoidEachOther_of_avoid_of_noContact
    strict.toRoutesAvoidEachOther.reverse_left
  intro firstPoint firstMember secondPoint secondMember
  exact strict.2.2.2 firstPoint
    (List.mem_reverse.mp firstMember) secondPoint secondMember

/-- Strict separation is independently invariant under reversal of the
second route. -/
theorem RoutesStrictlyAvoidEachOther.reverse_right
    {first second : List Cell}
    (strict : RoutesStrictlyAvoidEachOther first second) :
    RoutesStrictlyAvoidEachOther first second.reverse :=
  strict.symm.reverse_left.symm

/-- Every listed contact is at the first route's head and the second
route's tail. -/
def RoutesMeetOnlyAtFirstHeadSecondTail
    (first second : List Cell) : Prop :=
  ∀ firstPoint ∈ first,
    ∀ secondPoint ∈ second,
      firstPoint = secondPoint →
        first.head? = some firstPoint ∧
          second.getLast? = some secondPoint

/-- Every listed contact occurs at the head of the first route and at an
outer endpoint of the second route. -/
def RoutesMeetOnlyAtFirstHead
    (first second : List Cell) : Prop :=
  ∀ firstPoint ∈ first,
    ∀ secondPoint ∈ second,
      firstPoint = secondPoint →
        first.head? = some firstPoint ∧
          RoutePointIsEndpoint second secondPoint

/-- Ordinary separation has first-head-only contact when the first route's
tail differs from both endpoints of the second route. -/
theorem RoutesAvoidEachOther.meetOnlyAtFirstHead_of_endpoints_ne
    {first second : List Cell}
    (avoid : RoutesAvoidEachOther first second)
    (lastHeadNe : first.getLast? ≠ second.head?)
    (lastLastNe : first.getLast? ≠ second.getLast?) :
    RoutesMeetOnlyAtFirstHead first second := by
  intro firstPoint firstMember secondPoint secondMember pointsEqual
  rcases List.mem_iff_get.mp firstMember with
    ⟨firstIndex, firstIndexed⟩
  rcases List.mem_iff_get.mp secondMember with
    ⟨secondIndex, secondIndexed⟩
  have indexedEqual :
      first.get firstIndex = second.get secondIndex :=
    firstIndexed.trans (pointsEqual.trans secondIndexed.symm)
  have endpoints := avoid.2.2.2 firstIndex secondIndex indexedEqual
  rw [firstIndexed, secondIndexed] at endpoints
  rcases endpoints.1 with firstHead | firstLast
  · exact ⟨firstHead, endpoints.2⟩
  · rcases endpoints.2 with secondHead | secondLast
    · exact
        (lastHeadNe
          (firstLast.trans
            ((congrArg some pointsEqual).trans secondHead.symm))).elim
    · exact
        (lastLastNe
          (firstLast.trans
            ((congrArg some pointsEqual).trans secondLast.symm))).elim

/-- Ordinary separation has first-tail-only contact when the first route's
head differs from both endpoints of the second route. -/
theorem RoutesAvoidEachOther.meetOnlyAtFirstTail_of_endpoints_ne
    {first second : List Cell}
    (avoid : RoutesAvoidEachOther first second)
    (headHeadNe : first.head? ≠ second.head?)
    (headLastNe : first.head? ≠ second.getLast?) :
    RoutesMeetOnlyAtFirstTail first second := by
  intro firstPoint firstMember secondPoint secondMember pointsEqual
  rcases List.mem_iff_get.mp firstMember with
    ⟨firstIndex, firstIndexed⟩
  rcases List.mem_iff_get.mp secondMember with
    ⟨secondIndex, secondIndexed⟩
  have indexedEqual :
      first.get firstIndex = second.get secondIndex :=
    firstIndexed.trans (pointsEqual.trans secondIndexed.symm)
  have endpoints := avoid.2.2.2 firstIndex secondIndex indexedEqual
  rw [firstIndexed, secondIndexed] at endpoints
  rcases endpoints.1 with firstHead | firstLast
  · rcases endpoints.2 with secondHead | secondLast
    · exact
        (headHeadNe
          (firstHead.trans
            ((congrArg some pointsEqual).trans secondHead.symm))).elim
    · exact
        (headLastNe
          (firstHead.trans
            ((congrArg some pointsEqual).trans secondLast.symm))).elim
  · exact ⟨firstLast, endpoints.2⟩

/-- Ordinary route separation has head/tail-only listed contact when the
other three endpoint pairings are unequal. -/
theorem RoutesAvoidEachOther.meetOnlyAtFirstHeadSecondTail_of_endpoints_ne
    {first second : List Cell}
    (avoid : RoutesAvoidEachOther first second)
    (headHeadNe : first.head? ≠ second.head?)
    (lastHeadNe : first.getLast? ≠ second.head?)
    (lastLastNe : first.getLast? ≠ second.getLast?) :
    RoutesMeetOnlyAtFirstHeadSecondTail first second := by
  intro firstPoint firstMember secondPoint secondMember pointsEqual
  rcases List.mem_iff_get.mp firstMember with
    ⟨firstIndex, firstIndexed⟩
  rcases List.mem_iff_get.mp secondMember with
    ⟨secondIndex, secondIndexed⟩
  have indexedEqual :
      first.get firstIndex = second.get secondIndex :=
    firstIndexed.trans (pointsEqual.trans secondIndexed.symm)
  have endpoints := avoid.2.2.2 firstIndex secondIndex indexedEqual
  rw [firstIndexed, secondIndexed] at endpoints
  rcases endpoints.1 with firstHead | firstLast <;>
    rcases endpoints.2 with secondHead | secondLast
  · exact
      (headHeadNe
        (firstHead.trans
          ((congrArg some pointsEqual).trans secondHead.symm))).elim
  · exact ⟨firstHead, secondLast⟩
  · exact
      (lastHeadNe
        (firstLast.trans
          ((congrArg some pointsEqual).trans secondHead.symm))).elim
  · exact
      (lastLastNe
        (firstLast.trans
          ((congrArg some pointsEqual).trans secondLast.symm))).elim

/-- Join two pairs of pieces when the four component pairings retain only
the outer endpoint combination appropriate to those pieces. -/
theorem RoutesAvoidEachOther.join_both_of_outer_endpoint_contacts
    {firstPrefix firstSuffix secondPrefix secondSuffix : List Cell}
    {firstMiddle secondMiddle : Cell}
    (prefixesAvoid :
      RoutesAvoidEachOther firstPrefix secondPrefix)
    (prefixContacts : RoutesMeetOnlyAtHeads firstPrefix secondPrefix)
    (firstPrefixSecondSuffixAvoid :
      RoutesAvoidEachOther firstPrefix secondSuffix)
    (firstPrefixSecondSuffixContacts :
      RoutesMeetOnlyAtFirstHeadSecondTail
        firstPrefix secondSuffix)
    (firstSuffixSecondPrefixAvoid :
      RoutesAvoidEachOther firstSuffix secondPrefix)
    (firstSuffixSecondPrefixContacts :
      RoutesMeetOnlyAtFirstHeadSecondTail
        secondPrefix firstSuffix)
    (suffixesAvoid :
      RoutesAvoidEachOther firstSuffix secondSuffix)
    (suffixContacts :
      RoutesMeetOnlyAtTails firstSuffix secondSuffix)
    (firstEntrance : firstPrefix.getLast? = some firstMiddle)
    (firstSuffixHead : firstSuffix.head? = some firstMiddle)
    (secondEntrance : secondPrefix.getLast? = some secondMiddle)
    (secondSuffixHead : secondSuffix.head? = some secondMiddle) :
    RoutesAvoidEachOther
      (joinAtEndpoint firstPrefix firstSuffix)
      (joinAtEndpoint secondPrefix secondSuffix) := by
  have firstSegments :=
    gridPolylineSegments_joinAtEndpoint
      firstEntrance firstSuffixHead
  have secondSegments :=
    gridPolylineSegments_joinAtEndpoint
      secondEntrance secondSuffixHead
  apply routesAvoidEachOther_of_mem
  · intro firstSegment firstMember secondSegment secondMember
    rw [firstSegments, List.mem_append] at firstMember
    rw [secondSegments, List.mem_append] at secondMember
    rcases firstMember with firstPrefixMember | firstSuffixMember <;>
      rcases secondMember with secondPrefixMember | secondSuffixMember
    · exact prefixesAvoid.segmentsAvoid_of_mem
        _ firstPrefixMember _ secondPrefixMember
    · exact firstPrefixSecondSuffixAvoid.segmentsAvoid_of_mem
        _ firstPrefixMember _ secondSuffixMember
    · exact firstSuffixSecondPrefixAvoid.segmentsAvoid_of_mem
        _ firstSuffixMember _ secondPrefixMember
    · exact suffixesAvoid.segmentsAvoid_of_mem
        _ firstSuffixMember _ secondSuffixMember
  · intro firstPoint firstMember secondSegment secondMember
    rcases mem_joinAtEndpoint firstMember with
        firstPrefixMember | firstSuffixMember <;>
      rw [secondSegments, List.mem_append] at secondMember <;>
      rcases secondMember with secondPrefixMember | secondSuffixMember
    · exact prefixesAvoid.firstPointsAvoid_of_mem
        _ firstPrefixMember _ secondPrefixMember
    · exact firstPrefixSecondSuffixAvoid.firstPointsAvoid_of_mem
        _ firstPrefixMember _ secondSuffixMember
    · exact firstSuffixSecondPrefixAvoid.firstPointsAvoid_of_mem
        _ firstSuffixMember _ secondPrefixMember
    · exact suffixesAvoid.firstPointsAvoid_of_mem
        _ firstSuffixMember _ secondSuffixMember
  · intro secondPoint secondMember firstSegment firstMember
    rcases mem_joinAtEndpoint secondMember with
        secondPrefixMember | secondSuffixMember <;>
      rw [firstSegments, List.mem_append] at firstMember <;>
      rcases firstMember with firstPrefixMember | firstSuffixMember
    · exact prefixesAvoid.secondPointsAvoid_of_mem
        _ secondPrefixMember _ firstPrefixMember
    · exact firstSuffixSecondPrefixAvoid.secondPointsAvoid_of_mem
        _ secondPrefixMember _ firstSuffixMember
    · exact firstPrefixSecondSuffixAvoid.secondPointsAvoid_of_mem
        _ secondSuffixMember _ firstPrefixMember
    · exact suffixesAvoid.secondPointsAvoid_of_mem
        _ secondSuffixMember _ firstSuffixMember
  · intro firstPoint firstMember secondPoint secondMember equal
    rcases mem_joinAtEndpoint firstMember with
        firstPrefixMember | firstSuffixMember
    · rcases mem_joinAtEndpoint secondMember with
          secondPrefixMember | secondSuffixMember
      · have heads := prefixContacts
          _ firstPrefixMember _ secondPrefixMember equal
        exact
          ⟨Or.inl (joinAtEndpoint_head? heads.1),
            Or.inl (joinAtEndpoint_head? heads.2)⟩
      · have outer := firstPrefixSecondSuffixContacts
          _ firstPrefixMember _ secondSuffixMember equal
        exact
          ⟨Or.inl (joinAtEndpoint_head? outer.1),
            Or.inr (joinAtEndpoint_getLast?
              secondEntrance secondSuffixHead outer.2)⟩
    · rcases mem_joinAtEndpoint secondMember with
          secondPrefixMember | secondSuffixMember
      · have outer := firstSuffixSecondPrefixContacts
          _ secondPrefixMember _ firstSuffixMember equal.symm
        exact
          ⟨Or.inr (joinAtEndpoint_getLast?
              firstEntrance firstSuffixHead outer.2),
            Or.inl (joinAtEndpoint_head? outer.1)⟩
      · have tails := suffixContacts
          _ firstSuffixMember _ secondSuffixMember equal
        exact
          ⟨Or.inr (joinAtEndpoint_getLast?
              firstEntrance firstSuffixHead tails.1),
            Or.inr (joinAtEndpoint_getLast?
              secondEntrance secondSuffixHead tails.2)⟩

/-- Joining a prefix and suffix preserves separation from a single route
when their only contacts lie at the two outer endpoints of the join. -/
theorem RoutesAvoidEachOther.join_left_of_outer_endpoint_contacts
    {firstPiece suffix second : List Cell} {middle : Cell}
    (prefixAvoid : RoutesAvoidEachOther firstPiece second)
    (prefixContacts : RoutesMeetOnlyAtFirstHead firstPiece second)
    (suffixAvoid : RoutesAvoidEachOther suffix second)
    (suffixContacts : RoutesMeetOnlyAtFirstTail suffix second)
    (entrance : firstPiece.getLast? = some middle)
    (suffixHead : suffix.head? = some middle) :
    RoutesAvoidEachOther (joinAtEndpoint firstPiece suffix) second := by
  have joinedSegments :=
    gridPolylineSegments_joinAtEndpoint entrance suffixHead
  apply routesAvoidEachOther_of_mem
  · intro joinedSegment joinedMember secondSegment secondMember
    rw [joinedSegments, List.mem_append] at joinedMember
    rcases joinedMember with prefixMember | suffixMember
    · exact prefixAvoid.segmentsAvoid_of_mem
        _ prefixMember _ secondMember
    · exact suffixAvoid.segmentsAvoid_of_mem
        _ suffixMember _ secondMember
  · intro joinedPoint joinedMember secondSegment secondMember
    rcases mem_joinAtEndpoint joinedMember with
      prefixMember | suffixMember
    · exact prefixAvoid.firstPointsAvoid_of_mem
        _ prefixMember _ secondMember
    · exact suffixAvoid.firstPointsAvoid_of_mem
        _ suffixMember _ secondMember
  · intro secondPoint secondMember joinedSegment joinedMember
    rw [joinedSegments, List.mem_append] at joinedMember
    rcases joinedMember with prefixMember | suffixMember
    · exact prefixAvoid.secondPointsAvoid_of_mem
        _ secondMember _ prefixMember
    · exact suffixAvoid.secondPointsAvoid_of_mem
        _ secondMember _ suffixMember
  · intro joinedPoint joinedMember secondPoint secondMember equal
    rcases mem_joinAtEndpoint joinedMember with
      prefixMember | suffixMember
    · have outer := prefixContacts
        _ prefixMember _ secondMember equal
      exact ⟨Or.inl (joinAtEndpoint_head? outer.1), outer.2⟩
    · have outer := suffixContacts
        _ suffixMember _ secondMember equal
      exact
        ⟨Or.inr (joinAtEndpoint_getLast?
            entrance suffixHead outer.1), outer.2⟩

end PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

namespace PeriodicThreeDM

/-- An actual colored-element incidence recovers the concrete periodic edge
represented by its tag. -/
theorem incidenceEdgeAt_of_incidence_mem
    (problem : PeriodicThreeDM) (color : WireColor) (atom : Nat)
    {incidence : Incidence}
    (member : incidence ∈ problem.incidences color atom) :
    problem.incidenceEdgeAt ⟨incidence.tripleIndex, color⟩ =
      ⟨.triple incidence.tripleIndex, .element color atom,
        incidence.offset⟩ := by
  have tagMember :=
    incidenceTag_mem_of_incidence_mem problem color atom member
  have reference :=
    reference_eq_of_incidence_mem problem color atom member
  rw [incidenceEdgeAt_eq_of_tag_mem problem tagMember]
  simp only [incidenceEdge]
  have indexLt :=
    incidence_tripleIndex_lt problem color atom member
  rw [List.getD_eq_getElem _ _ indexLt] at reference
  rw [reference.1, reference.2]

/-- Global contracted-edge membership can always be specialized to the
colored element recorded in the edge itself. -/
theorem contractedEdge_mem_own_element
    (problem : PeriodicThreeDM) {edge : ContractedEdge}
    (member : edge ∈ problem.contractedEdges) :
    edge ∈ problem.contractedEdgesForElement edge.color edge.atom := by
  simp only [contractedEdges, List.mem_flatMap] at member
  rcases member with ⟨color, colorMember, member⟩
  simp only [contractedEdgesForColor, List.mem_flatMap] at member
  rcases member with ⟨atom, atomMember, member⟩
  have metadata :=
    contractedEdgesForElement_metadata problem color atom member
  rw [metadata.1, metadata.2]
  exact member

/-- The incidence facts attached to an emitted edge, stated at the edge's
own color and atom. -/
theorem contractedEdge_incidence_members_of_mem
    (problem : PeriodicThreeDM) {edge : ContractedEdge}
    (member : edge ∈ problem.contractedEdges) :
    edge.sourceIncidence ∈
        problem.incidences edge.color edge.atom ∧
      edge.targetIncidence ∈
        problem.incidences edge.color edge.atom ∧
      (problem.degree edge.color edge.atom = 2 ∧
          edge.targetIsElement = false ∨
        problem.degree edge.color edge.atom = 3 ∧
          edge.targetIsElement = true) := by
  exact contractedEdgesForElement_incidence_members
    problem edge.color edge.atom
      (contractedEdge_mem_own_element problem member)

/-- Lifted positions of listed incidence-graph vertices are injective in
both the prototype vertex and the lattice translate. -/
theorem PlanarPresentation.incidenceVertexOccurrence_injective
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    {first second : PeriodicThreeDMVertex}
    (firstMember : first ∈ problem.incidenceGraph.vertices)
    (secondMember : second ∈ problem.incidenceGraph.vertices)
    {firstTranslate secondTranslate : Cell}
    (equal :
      Cell.add
          (presentation.drawing.vertexPosition
            problem.incidenceGraph first)
          (presentation.drawing.periodTranslation firstTranslate) =
        Cell.add
          (presentation.drawing.vertexPosition
            problem.incidenceGraph second)
          (presentation.drawing.periodTranslation secondTranslate)) :
    first = second ∧ firstTranslate = secondTranslate := by
  have firstPositionMember := presentation.vertexPosition_mem firstMember
  have secondPositionMember := presentation.vertexPosition_mem secondMember
  have occurrenceEqual :=
    PeriodicGridDrawing.fundamentalPointOccurrence_injective
      presentation.drawing
      (presentation.compatible.2.2.2.2.1 _ firstPositionMember)
      (presentation.compatible.2.2.2.2.1 _ secondPositionMember)
      equal
  exact
    ⟨presentation.vertexPosition_injective_on
        firstMember secondMember occurrenceEqual.1,
      occurrenceEqual.2⟩

/-- Distinct syntactic incidence-vertex occurrences have distinct lifted
geometric positions. -/
theorem PlanarPresentation.incidenceVertexOccurrences_ne
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    {first second : PeriodicThreeDMVertex}
    (firstMember : first ∈ problem.incidenceGraph.vertices)
    (secondMember : second ∈ problem.incidenceGraph.vertices)
    {firstTranslate secondTranslate : Cell}
    (different : (first, firstTranslate) ≠ (second, secondTranslate)) :
    Cell.add
        (presentation.drawing.vertexPosition
          problem.incidenceGraph first)
        (presentation.drawing.periodTranslation firstTranslate) ≠
      Cell.add
        (presentation.drawing.vertexPosition
          problem.incidenceGraph second)
        (presentation.drawing.periodTranslation secondTranslate) := by
  intro equal
  have occurrenceEqual :=
    presentation.incidenceVertexOccurrence_injective
      firstMember secondMember equal
  exact different (Prod.ext occurrenceEqual.1 occurrenceEqual.2)

/-- One original incidence route realized at an arbitrary lattice
translate. -/
def PlanarPresentation.incidenceRouteOccurrence
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (tag : IncidenceTag) (translate : Cell) : List Cell :=
  translatePolyline
    (presentation.drawing.periodTranslation translate)
    (presentation.incidenceRoute tag)

/-- Exact lifted endpoints of an original incidence route occurrence. -/
theorem PlanarPresentation.incidenceRouteOccurrence_endpoints
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    {tag : IncidenceTag} (tagMember : tag ∈ problem.incidenceTags)
    (translate : Cell) :
    let edge := problem.incidenceEdgeAt tag
    (presentation.incidenceRouteOccurrence tag translate).head? =
        some (Cell.add
          (presentation.drawing.vertexPosition
            problem.incidenceGraph edge.source)
          (presentation.drawing.periodTranslation translate)) ∧
      (presentation.incidenceRouteOccurrence tag translate).getLast? =
        some (Cell.add
          (presentation.drawing.vertexPosition
            problem.incidenceGraph edge.target)
          (presentation.drawing.periodTranslation
            (Cell.add edge.offset translate))) := by
  dsimp only
  have endpoints := presentation.incidenceRoute_endpoints tagMember
  constructor
  · simp only [PlanarPresentation.incidenceRouteOccurrence,
      translatePolyline, List.head?_map, endpoints.1, Option.map_some]
    rcases presentation.drawing.vertexPosition
        problem.incidenceGraph (problem.incidenceEdgeAt tag).source with
      ⟨vertexX, vertexY⟩
    rcases presentation.drawing.periodTranslation translate with
      ⟨translateX, translateY⟩
    simp [Cell.add, add_comm]
  · simp only [PlanarPresentation.incidenceRouteOccurrence,
      translatePolyline, List.getLast?_map, endpoints.2, Option.map_some]
    rw [periodTranslation_add]
    rcases presentation.drawing.vertexPosition
        problem.incidenceGraph (problem.incidenceEdgeAt tag).target with
      ⟨vertexX, vertexY⟩
    rcases presentation.drawing.periodTranslation
        (problem.incidenceEdgeAt tag).offset with
      ⟨offsetX, offsetY⟩
    rcases presentation.drawing.periodTranslation translate with
      ⟨translateX, translateY⟩
    simp [Cell.add, add_comm, add_left_comm]

/-- Complete lifted separation of the source drawing specializes to any
two distinct incidence-tag occurrences. -/
theorem PlanarPresentation.incidenceRouteOccurrences_avoidEachOther
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (separated : presentation.drawing.LiftedRoutesAvoidEachOther)
    {firstTag secondTag : IncidenceTag}
    (firstMember : firstTag ∈ problem.incidenceTags)
    (secondMember : secondTag ∈ problem.incidenceTags)
    (firstTranslate secondTranslate : Cell)
    (different :
      (firstTag, firstTranslate) ≠ (secondTag, secondTranslate)) :
    RoutesAvoidEachOther
      (presentation.incidenceRouteOccurrence firstTag firstTranslate)
      (presentation.incidenceRouteOccurrence secondTag secondTranslate) := by
  have occurrenceDifferent :
      (problem.incidenceRouteIndex firstTag, firstTranslate) ≠
        (problem.incidenceRouteIndex secondTag, secondTranslate) := by
    intro equal
    apply different
    rcases Prod.mk.inj equal with ⟨indexEqual, translateEqual⟩
    exact Prod.ext
      ((List.idxOf_inj firstMember).mp indexEqual)
      translateEqual
  exact
    separated
      (presentation.incidenceRoute firstTag,
        problem.incidenceRouteIndex firstTag)
      (presentation.incidenceRoute_zipIdx_mem firstMember)
      (presentation.incidenceRoute secondTag,
        problem.incidenceRouteIndex secondTag)
      (presentation.incidenceRoute_zipIdx_mem secondMember)
      firstTranslate secondTranslate occurrenceDifferent

/-- Endpoint inequality between two incidence occurrences follows from
inequality of their corresponding lifted source vertices. -/
theorem PlanarPresentation.incidenceRouteOccurrence_head_ne_head
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    {firstTag secondTag : IncidenceTag}
    (firstMember : firstTag ∈ problem.incidenceTags)
    (secondMember : secondTag ∈ problem.incidenceTags)
    (firstTranslate secondTranslate : Cell)
    (different :
      ((problem.incidenceEdgeAt firstTag).source, firstTranslate) ≠
        ((problem.incidenceEdgeAt secondTag).source, secondTranslate)) :
    (presentation.incidenceRouteOccurrence
        firstTag firstTranslate).head? ≠
      (presentation.incidenceRouteOccurrence
        secondTag secondTranslate).head? := by
  have firstEdgeMember := List.fst_mem_of_mem_zipIdx
    (incidenceEdge_zipIdx_mem problem firstMember)
  have secondEdgeMember := List.fst_mem_of_mem_zipIdx
    (incidenceEdge_zipIdx_mem problem secondMember)
  have firstVertexMember :=
    (presentation.incidenceGraph_isWellFormed.2 _ firstEdgeMember).1
  have secondVertexMember :=
    (presentation.incidenceGraph_isWellFormed.2 _ secondEdgeMember).1
  have positionsNe := presentation.incidenceVertexOccurrences_ne
    firstVertexMember secondVertexMember different
  rw [(presentation.incidenceRouteOccurrence_endpoints
      firstMember firstTranslate).1,
    (presentation.incidenceRouteOccurrence_endpoints
      secondMember secondTranslate).1]
  exact fun equal => positionsNe (Option.some.inj equal)

/-- A source endpoint cannot equal a target endpoint when their syntactic
lifted vertex occurrences differ. -/
theorem PlanarPresentation.incidenceRouteOccurrence_head_ne_last
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    {firstTag secondTag : IncidenceTag}
    (firstMember : firstTag ∈ problem.incidenceTags)
    (secondMember : secondTag ∈ problem.incidenceTags)
    (firstTranslate secondTranslate : Cell)
    (different :
      ((problem.incidenceEdgeAt firstTag).source, firstTranslate) ≠
        ((problem.incidenceEdgeAt secondTag).target,
          Cell.add (problem.incidenceEdgeAt secondTag).offset
            secondTranslate)) :
    (presentation.incidenceRouteOccurrence
        firstTag firstTranslate).head? ≠
      (presentation.incidenceRouteOccurrence
        secondTag secondTranslate).getLast? := by
  have firstEdgeMember := List.fst_mem_of_mem_zipIdx
    (incidenceEdge_zipIdx_mem problem firstMember)
  have secondEdgeMember := List.fst_mem_of_mem_zipIdx
    (incidenceEdge_zipIdx_mem problem secondMember)
  have firstVertexMember :=
    (presentation.incidenceGraph_isWellFormed.2 _ firstEdgeMember).1
  have secondVertexMember :=
    (presentation.incidenceGraph_isWellFormed.2 _ secondEdgeMember).2
  have positionsNe := presentation.incidenceVertexOccurrences_ne
    firstVertexMember secondVertexMember different
  rw [(presentation.incidenceRouteOccurrence_endpoints
      firstMember firstTranslate).1,
    (presentation.incidenceRouteOccurrence_endpoints
      secondMember secondTranslate).2]
  exact fun equal => positionsNe (Option.some.inj equal)

/-- A target endpoint cannot equal a source endpoint when their syntactic
lifted vertex occurrences differ. -/
theorem PlanarPresentation.incidenceRouteOccurrence_last_ne_head
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    {firstTag secondTag : IncidenceTag}
    (firstMember : firstTag ∈ problem.incidenceTags)
    (secondMember : secondTag ∈ problem.incidenceTags)
    (firstTranslate secondTranslate : Cell)
    (different :
      ((problem.incidenceEdgeAt firstTag).target,
          Cell.add (problem.incidenceEdgeAt firstTag).offset
            firstTranslate) ≠
        ((problem.incidenceEdgeAt secondTag).source, secondTranslate)) :
    (presentation.incidenceRouteOccurrence
        firstTag firstTranslate).getLast? ≠
      (presentation.incidenceRouteOccurrence
        secondTag secondTranslate).head? := by
  exact fun equal =>
    presentation.incidenceRouteOccurrence_head_ne_last
      secondMember firstMember secondTranslate firstTranslate
      (fun occurrenceEqual => different occurrenceEqual.symm)
      equal.symm

/-- Target endpoint inequality is likewise purely syntactic. -/
theorem PlanarPresentation.incidenceRouteOccurrence_last_ne_last
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    {firstTag secondTag : IncidenceTag}
    (firstMember : firstTag ∈ problem.incidenceTags)
    (secondMember : secondTag ∈ problem.incidenceTags)
    (firstTranslate secondTranslate : Cell)
    (different :
      ((problem.incidenceEdgeAt firstTag).target,
          Cell.add (problem.incidenceEdgeAt firstTag).offset
            firstTranslate) ≠
        ((problem.incidenceEdgeAt secondTag).target,
          Cell.add (problem.incidenceEdgeAt secondTag).offset
            secondTranslate)) :
    (presentation.incidenceRouteOccurrence
        firstTag firstTranslate).getLast? ≠
      (presentation.incidenceRouteOccurrence
        secondTag secondTranslate).getLast? := by
  have firstEdgeMember := List.fst_mem_of_mem_zipIdx
    (incidenceEdge_zipIdx_mem problem firstMember)
  have secondEdgeMember := List.fst_mem_of_mem_zipIdx
    (incidenceEdge_zipIdx_mem problem secondMember)
  have firstVertexMember :=
    (presentation.incidenceGraph_isWellFormed.2 _ firstEdgeMember).2
  have secondVertexMember :=
    (presentation.incidenceGraph_isWellFormed.2 _ secondEdgeMember).2
  have positionsNe := presentation.incidenceVertexOccurrences_ne
    firstVertexMember secondVertexMember different
  rw [(presentation.incidenceRouteOccurrence_endpoints
      firstMember firstTranslate).2,
    (presentation.incidenceRouteOccurrence_endpoints
      secondMember secondTranslate).2]
  exact fun equal => positionsNe (Option.some.inj equal)

/-- One optionally reversed original incidence-route occurrence used as a
piece of a contracted route. -/
structure ContractedRoutePiece where
  tag : IncidenceTag
  latticeShift : Cell
  reversed : Bool
  deriving DecidableEq, Repr

namespace ContractedEdge

/-- The source-side incidence-route occurrence of a contracted edge. -/
def sourcePiece (edge : ContractedEdge) (translate : Cell) :
    ContractedRoutePiece where
  tag := edge.sourceTag
  latticeShift := translate
  reversed := false

/-- The reversed target-side incidence-route occurrence of a through edge.
Its base translate is shifted by the contracted edge offset. -/
def throughTargetPiece
    (color : WireColor) (_atom : Nat)
    (first second : Incidence) (translate : Cell) :
    ContractedRoutePiece where
  tag := (⟨second.tripleIndex, color⟩ : IncidenceTag)
  latticeShift := Cell.add (Cell.sub first.offset second.offset) translate
  reversed := true

end ContractedEdge

/-- Physical route represented by one contracted-route piece. -/
def ContractedRoutePiece.route
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (piece : ContractedRoutePiece) : List Cell :=
  let occurrence :=
    presentation.incidenceRouteOccurrence piece.tag piece.latticeShift
  if piece.reversed then occurrence.reverse else occurrence

/-- Lifted incidence-graph vertex occurrence at the beginning of a piece. -/
def ContractedRoutePiece.startOccurrence
    (problem : PeriodicThreeDM)
    (piece : ContractedRoutePiece) : PeriodicThreeDMVertex × Cell :=
  let edge := problem.incidenceEdgeAt piece.tag
  if piece.reversed then
    (edge.target, Cell.add edge.offset piece.latticeShift)
  else
    (edge.source, piece.latticeShift)

/-- Lifted incidence-graph vertex occurrence at the end of a piece. -/
def ContractedRoutePiece.finishOccurrence
    (problem : PeriodicThreeDM)
    (piece : ContractedRoutePiece) : PeriodicThreeDMVertex × Cell :=
  let edge := problem.incidenceEdgeAt piece.tag
  if piece.reversed then
    (edge.source, piece.latticeShift)
  else
    (edge.target, Cell.add edge.offset piece.latticeShift)

/-- The source piece of an emitted edge names a genuine incidence route. -/
theorem ContractedEdge.sourcePiece_tag_mem
    (problem : PeriodicThreeDM) {edge : ContractedEdge}
    (edgeMember : edge ∈ problem.contractedEdges) (translate : Cell) :
    (edge.sourcePiece translate).tag ∈ problem.incidenceTags := by
  apply incidenceTag_mem_of_contractedEdge problem edgeMember
  cases edge <;> simp [ContractedEdge.sourcePiece,
    ContractedEdge.incidenceTags, ContractedEdge.sourceTag]

/-- The target piece of an emitted through edge names its second genuine
incidence route. -/
theorem ContractedEdge.throughTargetPiece_tag_mem
    (problem : PeriodicThreeDM)
    {color : WireColor} {atom : Nat} {first second : Incidence}
    (edgeMember :
      .through color atom first second ∈ problem.contractedEdges)
    (translate : Cell) :
    (ContractedEdge.throughTargetPiece
      color atom first second translate).tag ∈
        problem.incidenceTags := by
  apply incidenceTag_mem_of_contractedEdge problem edgeMember
  simp [ContractedEdge.throughTargetPiece,
    ContractedEdge.incidenceTags, ContractedEdge.targetTag]

/-- The source piece starts at the source occurrence of the contracted
edge. -/
theorem ContractedEdge.sourcePiece_startOccurrence
    (problem : PeriodicThreeDM) {edge : ContractedEdge}
    (edgeMember : edge ∈ problem.contractedEdges) (translate : Cell) :
    (edge.sourcePiece translate).startOccurrence problem =
      (edge.toPeriodicEdge.source, translate) := by
  have incidenceMembers :=
    contractedEdge_incidence_members_of_mem problem edgeMember
  cases edge with
  | retained color atom incidence =>
      simp only [ContractedEdge.sourceIncidence,
        ContractedEdge.color, ContractedEdge.atom] at incidenceMembers
      simp only [ContractedEdge.sourcePiece,
        ContractedRoutePiece.startOccurrence,
        ContractedEdge.sourceTag]
      rw [incidenceEdgeAt_of_incidence_mem
        problem color atom (incidence := incidence) incidenceMembers.1]
      simp [ContractedEdge.toPeriodicEdge]
  | through color atom first second =>
      simp only [ContractedEdge.sourceIncidence,
        ContractedEdge.color, ContractedEdge.atom] at incidenceMembers
      simp only [ContractedEdge.sourcePiece,
        ContractedRoutePiece.startOccurrence,
        ContractedEdge.sourceTag]
      rw [incidenceEdgeAt_of_incidence_mem
        problem color atom (incidence := first) incidenceMembers.1]
      simp [ContractedEdge.toPeriodicEdge]

/-- On a retained edge the source piece also finishes at the contracted
edge's target occurrence. -/
theorem ContractedEdge.sourcePiece_finishOccurrence_retained
    (problem : PeriodicThreeDM)
    {color : WireColor} {atom : Nat} {incidence : Incidence}
    (edgeMember :
      ContractedEdge.retained color atom incidence ∈
        problem.contractedEdges)
    (translate : Cell) :
    ContractedRoutePiece.finishOccurrence problem
        ((ContractedEdge.retained color atom incidence).sourcePiece
          translate) =
      ((.element color atom), Cell.add incidence.offset translate) := by
  have incidenceMember :
      incidence ∈ problem.incidences color atom := by
    simpa [ContractedEdge.sourceIncidence, ContractedEdge.color,
      ContractedEdge.atom] using
      (contractedEdge_incidence_members_of_mem problem edgeMember).1
  simp only [ContractedEdge.sourcePiece,
    ContractedRoutePiece.finishOccurrence, ContractedEdge.sourceTag]
  rw [incidenceEdgeAt_of_incidence_mem
    problem color atom (incidence := incidence) incidenceMember]
  simp

/-- The source half of a through edge ends at its suppressed element
occurrence. -/
theorem ContractedEdge.sourcePiece_finishOccurrence_through
    (problem : PeriodicThreeDM)
    {color : WireColor} {atom : Nat} {first second : Incidence}
    (edgeMember :
      ContractedEdge.through color atom first second ∈
        problem.contractedEdges)
    (translate : Cell) :
    ContractedRoutePiece.finishOccurrence problem
        ((ContractedEdge.through color atom first second).sourcePiece
          translate) =
      ((.element color atom), Cell.add first.offset translate) := by
  have incidenceMember :
      first ∈ problem.incidences color atom := by
    simpa [ContractedEdge.sourceIncidence, ContractedEdge.color,
      ContractedEdge.atom] using
      (contractedEdge_incidence_members_of_mem problem edgeMember).1
  simp only [ContractedEdge.sourcePiece,
    ContractedRoutePiece.finishOccurrence, ContractedEdge.sourceTag]
  rw [incidenceEdgeAt_of_incidence_mem
    problem color atom (incidence := first) incidenceMember]
  simp

/-- The reversed target half begins at the same suppressed-element
occurrence as the source half ends. -/
theorem ContractedEdge.throughTargetPiece_startOccurrence
    (problem : PeriodicThreeDM)
    {color : WireColor} {atom : Nat} {first second : Incidence}
    (edgeMember :
      ContractedEdge.through color atom first second ∈
        problem.contractedEdges)
    (translate : Cell) :
    ContractedRoutePiece.startOccurrence problem
        (ContractedEdge.throughTargetPiece
          color atom first second translate) =
      ((.element color atom), Cell.add first.offset translate) := by
  have incidenceMember :
      second ∈ problem.incidences color atom := by
    simpa [ContractedEdge.targetIncidence, ContractedEdge.color,
      ContractedEdge.atom] using
      (contractedEdge_incidence_members_of_mem problem edgeMember).2.1
  simp only [ContractedEdge.throughTargetPiece,
    ContractedRoutePiece.startOccurrence]
  rw [incidenceEdgeAt_of_incidence_mem
    problem color atom (incidence := second) incidenceMember]
  simp [Cell.add, Cell.sub]
  constructor <;> ring

/-- The reversed target half finishes at the target occurrence of the
contracted through edge. -/
theorem ContractedEdge.throughTargetPiece_finishOccurrence
    (problem : PeriodicThreeDM)
    {color : WireColor} {atom : Nat} {first second : Incidence}
    (edgeMember :
      ContractedEdge.through color atom first second ∈
        problem.contractedEdges)
    (translate : Cell) :
    ContractedRoutePiece.finishOccurrence problem
        (ContractedEdge.throughTargetPiece
          color atom first second translate) =
      ((.triple second.tripleIndex),
        Cell.add (Cell.sub first.offset second.offset) translate) := by
  have incidenceMember :
      second ∈ problem.incidences color atom := by
    simpa [ContractedEdge.targetIncidence, ContractedEdge.color,
      ContractedEdge.atom] using
      (contractedEdge_incidence_members_of_mem problem edgeMember).2.1
  simp only [ContractedEdge.throughTargetPiece,
    ContractedRoutePiece.finishOccurrence]
  rw [incidenceEdgeAt_of_incidence_mem
    problem color atom (incidence := second) incidenceMember]
  simp

/-- A piece's physical route has the endpoints recorded in its occurrence
metadata. -/
theorem ContractedRoutePiece.route_endpoints
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (piece : ContractedRoutePiece)
    (tagMember : piece.tag ∈ problem.incidenceTags) :
    (piece.route presentation).head? =
        some (Cell.add
          (presentation.drawing.vertexPosition problem.incidenceGraph
            (piece.startOccurrence problem).1)
          (presentation.drawing.periodTranslation
            (piece.startOccurrence problem).2)) ∧
      (piece.route presentation).getLast? =
        some (Cell.add
          (presentation.drawing.vertexPosition problem.incidenceGraph
            (piece.finishOccurrence problem).1)
          (presentation.drawing.periodTranslation
            (piece.finishOccurrence problem).2)) := by
  have endpoints :=
    presentation.incidenceRouteOccurrence_endpoints
      tagMember piece.latticeShift
  cases reversedEq : piece.reversed
  · simpa [ContractedRoutePiece.route, ContractedRoutePiece.startOccurrence,
      ContractedRoutePiece.finishOccurrence, reversedEq] using endpoints
  · constructor
    · simpa [ContractedRoutePiece.route,
        ContractedRoutePiece.startOccurrence,
        ContractedRoutePiece.finishOccurrence, reversedEq] using endpoints.2
    · simpa [ContractedRoutePiece.route,
        ContractedRoutePiece.startOccurrence,
        ContractedRoutePiece.finishOccurrence, reversedEq] using endpoints.1

/-- Different piece metadata name different source route occurrences. -/
def ContractedRoutePiece.SourceOccurrenceDifferent
    (first second : ContractedRoutePiece) : Prop :=
  (first.tag, first.latticeShift) ≠
    (second.tag, second.latticeShift)

/-- Source lifted-route separation is invariant under the optional
traversal reversals carried by two pieces. -/
theorem PlanarPresentation.contractedRoutePieces_avoidEachOther
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (separated : presentation.drawing.LiftedRoutesAvoidEachOther)
    (first second : ContractedRoutePiece)
    (firstMember : first.tag ∈ problem.incidenceTags)
    (secondMember : second.tag ∈ problem.incidenceTags)
    (different : first.SourceOccurrenceDifferent second) :
    RoutesAvoidEachOther
      (first.route presentation) (second.route presentation) := by
  have avoids :=
    presentation.incidenceRouteOccurrences_avoidEachOther separated
      firstMember secondMember first.latticeShift second.latticeShift
      different
  cases firstReversed : first.reversed <;>
    cases secondReversed : second.reversed
  · simpa [ContractedRoutePiece.route, firstReversed,
      secondReversed] using avoids
  · simpa [ContractedRoutePiece.route, firstReversed,
      secondReversed] using avoids.reverse_right
  · simpa [ContractedRoutePiece.route, firstReversed,
      secondReversed] using avoids.reverse_left
  · simpa [ContractedRoutePiece.route, firstReversed,
      secondReversed] using routesAvoidEachOther_reverse avoids

/-- Distinct recorded endpoint occurrences give distinct geometric
endpoints of two pieces. -/
theorem PlanarPresentation.contractedRoutePiece_endpoints_ne
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (first second : ContractedRoutePiece)
    (firstMember : first.tag ∈ problem.incidenceTags)
    (secondMember : second.tag ∈ problem.incidenceTags)
    (firstEndpoint : Bool) (secondEndpoint : Bool)
    (different :
      (if firstEndpoint then first.finishOccurrence problem
        else first.startOccurrence problem) ≠
      (if secondEndpoint then second.finishOccurrence problem
        else second.startOccurrence problem)) :
    (if firstEndpoint then (first.route presentation).getLast?
        else (first.route presentation).head?) ≠
      (if secondEndpoint then (second.route presentation).getLast?
        else (second.route presentation).head?) := by
  let firstOccurrence :=
    if firstEndpoint then first.finishOccurrence problem
      else first.startOccurrence problem
  let secondOccurrence :=
    if secondEndpoint then second.finishOccurrence problem
      else second.startOccurrence problem
  have firstEdgeMember := List.fst_mem_of_mem_zipIdx
    (incidenceEdge_zipIdx_mem problem firstMember)
  have secondEdgeMember := List.fst_mem_of_mem_zipIdx
    (incidenceEdge_zipIdx_mem problem secondMember)
  have firstStartMember :=
    (presentation.incidenceGraph_isWellFormed.2 _ firstEdgeMember).1
  have firstFinishMember :=
    (presentation.incidenceGraph_isWellFormed.2 _ firstEdgeMember).2
  have secondStartMember :=
    (presentation.incidenceGraph_isWellFormed.2 _ secondEdgeMember).1
  have secondFinishMember :=
    (presentation.incidenceGraph_isWellFormed.2 _ secondEdgeMember).2
  have firstOccurrenceMember :
      firstOccurrence.1 ∈ problem.incidenceGraph.vertices := by
    cases firstEndpoint <;> by_cases reversed : first.reversed <;>
      simp [firstOccurrence, ContractedRoutePiece.startOccurrence,
        ContractedRoutePiece.finishOccurrence, reversed] <;>
      assumption
  have secondOccurrenceMember :
      secondOccurrence.1 ∈ problem.incidenceGraph.vertices := by
    cases secondEndpoint <;> by_cases reversed : second.reversed <;>
      simp [secondOccurrence, ContractedRoutePiece.startOccurrence,
        ContractedRoutePiece.finishOccurrence, reversed] <;>
      assumption
  have positionsNe :=
    presentation.incidenceVertexOccurrences_ne
      firstOccurrenceMember secondOccurrenceMember different
  have firstEndpoints := first.route_endpoints presentation firstMember
  have secondEndpoints := second.route_endpoints presentation secondMember
  cases firstEndpoint <;> cases secondEndpoint
  · simp [firstOccurrence, secondOccurrence] at positionsNe
    rw [firstEndpoints.1, secondEndpoints.1]
    exact fun equal => positionsNe (Option.some.inj equal)
  · simp [firstOccurrence, secondOccurrence] at positionsNe
    rw [firstEndpoints.1, secondEndpoints.2]
    exact fun equal => positionsNe (Option.some.inj equal)
  · simp [firstOccurrence, secondOccurrence] at positionsNe
    rw [firstEndpoints.2, secondEndpoints.1]
    exact fun equal => positionsNe (Option.some.inj equal)
  · simp [firstOccurrence, secondOccurrence] at positionsNe
    rw [firstEndpoints.2, secondEndpoints.2]
    exact fun equal => positionsNe (Option.some.inj equal)

/-- Four distinct endpoint pairings strengthen ordinary piece separation
to strict separation. -/
theorem PlanarPresentation.contractedRoutePieces_strictlyAvoidEachOther
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (separated : presentation.drawing.LiftedRoutesAvoidEachOther)
    (first second : ContractedRoutePiece)
    (firstMember : first.tag ∈ problem.incidenceTags)
    (secondMember : second.tag ∈ problem.incidenceTags)
    (sourceDifferent : first.SourceOccurrenceDifferent second)
    (startStart : first.startOccurrence problem ≠ second.startOccurrence problem)
    (startFinish : first.startOccurrence problem ≠ second.finishOccurrence problem)
    (finishStart : first.finishOccurrence problem ≠ second.startOccurrence problem)
    (finishFinish : first.finishOccurrence problem ≠ second.finishOccurrence problem) :
    RoutesStrictlyAvoidEachOther
      (first.route presentation) (second.route presentation) :=
  routesStrictlyAvoidEachOther_of_avoid_of_endpoints_ne
    (presentation.contractedRoutePieces_avoidEachOther separated
      first second firstMember secondMember sourceDifferent)
    (presentation.contractedRoutePiece_endpoints_ne
      first second firstMember secondMember false false startStart)
    (presentation.contractedRoutePiece_endpoints_ne
      first second firstMember secondMember false true startFinish)
    (presentation.contractedRoutePiece_endpoints_ne
      first second firstMember secondMember true false finishStart)
    (presentation.contractedRoutePiece_endpoints_ne
      first second firstMember secondMember true true finishFinish)

/-- If every non-head endpoint pairing is distinct, two separated pieces
can meet only at their heads. -/
theorem PlanarPresentation.contractedRoutePieces_meetOnlyAtHeads
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (separated : presentation.drawing.LiftedRoutesAvoidEachOther)
    (first second : ContractedRoutePiece)
    (firstMember : first.tag ∈ problem.incidenceTags)
    (secondMember : second.tag ∈ problem.incidenceTags)
    (sourceDifferent : first.SourceOccurrenceDifferent second)
    (startFinish : first.startOccurrence problem ≠ second.finishOccurrence problem)
    (finishStart : first.finishOccurrence problem ≠ second.startOccurrence problem)
    (finishFinish : first.finishOccurrence problem ≠ second.finishOccurrence problem) :
    RoutesMeetOnlyAtHeads
      (first.route presentation) (second.route presentation) :=
  (presentation.contractedRoutePieces_avoidEachOther separated
    first second firstMember secondMember sourceDifferent)
    |>.meetOnlyAtHeads_of_endpoints_ne
      (presentation.contractedRoutePiece_endpoints_ne
        first second firstMember secondMember false true startFinish)
      (presentation.contractedRoutePiece_endpoints_ne
        first second firstMember secondMember true false finishStart)
      (presentation.contractedRoutePiece_endpoints_ne
        first second firstMember secondMember true true finishFinish)

/-- Dually, if every non-tail endpoint pairing is distinct, contacts occur
only at the two tails. -/
theorem PlanarPresentation.contractedRoutePieces_meetOnlyAtTails
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (separated : presentation.drawing.LiftedRoutesAvoidEachOther)
    (first second : ContractedRoutePiece)
    (firstMember : first.tag ∈ problem.incidenceTags)
    (secondMember : second.tag ∈ problem.incidenceTags)
    (sourceDifferent : first.SourceOccurrenceDifferent second)
    (startStart : first.startOccurrence problem ≠ second.startOccurrence problem)
    (startFinish : first.startOccurrence problem ≠ second.finishOccurrence problem)
    (finishStart : first.finishOccurrence problem ≠ second.startOccurrence problem) :
    RoutesMeetOnlyAtTails
      (first.route presentation) (second.route presentation) :=
  (presentation.contractedRoutePieces_avoidEachOther separated
    first second firstMember secondMember sourceDifferent)
    |>.meetOnlyAtTails_of_endpoints_ne
      (presentation.contractedRoutePiece_endpoints_ne
        first second firstMember secondMember false false startStart)
      (presentation.contractedRoutePiece_endpoints_ne
        first second firstMember secondMember false true startFinish)
      (presentation.contractedRoutePiece_endpoints_ne
        first second firstMember secondMember true false finishStart)

/-- Endpoint inequalities specialize separated pieces to first-head-only
contact. -/
theorem PlanarPresentation.contractedRoutePieces_meetOnlyAtFirstHead
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (separated : presentation.drawing.LiftedRoutesAvoidEachOther)
    (first second : ContractedRoutePiece)
    (firstMember : first.tag ∈ problem.incidenceTags)
    (secondMember : second.tag ∈ problem.incidenceTags)
    (sourceDifferent : first.SourceOccurrenceDifferent second)
    (finishStart : first.finishOccurrence problem ≠ second.startOccurrence problem)
    (finishFinish : first.finishOccurrence problem ≠ second.finishOccurrence problem) :
    RoutesMeetOnlyAtFirstHead
      (first.route presentation) (second.route presentation) :=
  (presentation.contractedRoutePieces_avoidEachOther separated
    first second firstMember secondMember sourceDifferent)
    |>.meetOnlyAtFirstHead_of_endpoints_ne
      (presentation.contractedRoutePiece_endpoints_ne
        first second firstMember secondMember true false finishStart)
      (presentation.contractedRoutePiece_endpoints_ne
        first second firstMember secondMember true true finishFinish)

/-- Dually, endpoint inequalities specialize separated pieces to
first-tail-only contact. -/
theorem PlanarPresentation.contractedRoutePieces_meetOnlyAtFirstTail
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (separated : presentation.drawing.LiftedRoutesAvoidEachOther)
    (first second : ContractedRoutePiece)
    (firstMember : first.tag ∈ problem.incidenceTags)
    (secondMember : second.tag ∈ problem.incidenceTags)
    (sourceDifferent : first.SourceOccurrenceDifferent second)
    (startStart : first.startOccurrence problem ≠ second.startOccurrence problem)
    (startFinish : first.startOccurrence problem ≠ second.finishOccurrence problem) :
    RoutesMeetOnlyAtFirstTail
      (first.route presentation) (second.route presentation) :=
  (presentation.contractedRoutePieces_avoidEachOther separated
    first second firstMember secondMember sourceDifferent)
    |>.meetOnlyAtFirstTail_of_endpoints_ne
      (presentation.contractedRoutePiece_endpoints_ne
        first second firstMember secondMember false false startStart)
      (presentation.contractedRoutePiece_endpoints_ne
        first second firstMember secondMember false true startFinish)

/-- Endpoint inequalities specialize separated pieces to contact only at
the first head and second tail. -/
theorem PlanarPresentation.contractedRoutePieces_meetOnlyAtFirstHeadSecondTail
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (separated : presentation.drawing.LiftedRoutesAvoidEachOther)
    (first second : ContractedRoutePiece)
    (firstMember : first.tag ∈ problem.incidenceTags)
    (secondMember : second.tag ∈ problem.incidenceTags)
    (sourceDifferent : first.SourceOccurrenceDifferent second)
    (startStart : first.startOccurrence problem ≠ second.startOccurrence problem)
    (finishStart : first.finishOccurrence problem ≠ second.startOccurrence problem)
    (finishFinish : first.finishOccurrence problem ≠ second.finishOccurrence problem) :
    RoutesMeetOnlyAtFirstHeadSecondTail
      (first.route presentation) (second.route presentation) :=
  (presentation.contractedRoutePieces_avoidEachOther separated
    first second firstMember secondMember sourceDifferent)
    |>.meetOnlyAtFirstHeadSecondTail_of_endpoints_ne
      (presentation.contractedRoutePiece_endpoints_ne
        first second firstMember secondMember false false startStart)
      (presentation.contractedRoutePiece_endpoints_ne
        first second firstMember secondMember true false finishStart)
      (presentation.contractedRoutePiece_endpoints_ne
        first second firstMember secondMember true true finishFinish)

private theorem translatePolyline_joinAtEndpoint_local
    (offset : Cell) (first second : List Cell) :
    translatePolyline offset (joinAtEndpoint first second) =
      joinAtEndpoint
        (translatePolyline offset first)
        (translatePolyline offset second) := by
  simp [translatePolyline, joinAtEndpoint]

private theorem translatePolyline_add_local
    (first second : Cell) (points : List Cell) :
    translatePolyline second (translatePolyline first points) =
      translatePolyline (Cell.add first second) points := by
  unfold translatePolyline
  simp only [List.map_map]
  apply List.map_congr_left
  intro point pointMember
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  rcases point with ⟨pointX, pointY⟩
  simp [Cell.add]
  constructor <;> ring

/-- A contracted edge route realized at an arbitrary lattice translate. -/
def PlanarPresentation.contractedEdgeRouteOccurrence
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (edge : ContractedEdge) (translate : Cell) : List Cell :=
  translatePolyline
    (presentation.drawing.periodTranslation translate)
    (presentation.contractedEdgeRoute edge)

/-- A retained contracted route occurrence is exactly its single source
piece. -/
theorem PlanarPresentation.contractedEdgeRouteOccurrence_retained
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (color : WireColor) (atom : Nat) (incidence : Incidence)
    (translate : Cell) :
    presentation.contractedEdgeRouteOccurrence
        (ContractedEdge.retained color atom incidence) translate =
      ContractedRoutePiece.route presentation
        ((ContractedEdge.retained color atom incidence).sourcePiece
          translate) := by
  rfl

/-- A through contracted route occurrence is the endpoint join of its
source incidence and its translated, reversed target incidence. -/
theorem PlanarPresentation.contractedEdgeRouteOccurrence_through
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (color : WireColor) (atom : Nat) (first second : Incidence)
    (translate : Cell) :
    presentation.contractedEdgeRouteOccurrence
        (ContractedEdge.through color atom first second) translate =
      joinAtEndpoint
        (ContractedRoutePiece.route presentation
          ((ContractedEdge.through color atom first second).sourcePiece
            translate))
        (ContractedRoutePiece.route presentation
          (ContractedEdge.throughTargetPiece
            color atom first second translate)) := by
  unfold PlanarPresentation.contractedEdgeRouteOccurrence
  simp only [PlanarPresentation.contractedEdgeRoute]
  change
    translatePolyline (presentation.drawing.periodTranslation translate)
        (joinAtEndpoint
          (presentation.incidenceRoute
            ⟨first.tripleIndex, color⟩)
          (presentation.reversedIncidenceRouteAt
            color first second)) = _
  rw [translatePolyline_joinAtEndpoint_local]
  unfold PlanarPresentation.reversedIncidenceRouteAt
    ContractedEdge.sourcePiece
    ContractedEdge.throughTargetPiece
    ContractedRoutePiece.route
    PlanarPresentation.incidenceRouteOccurrence
  congr 1
  simp only [↓reduceIte]
  rw [show
    translatePolyline (presentation.drawing.periodTranslation translate)
        (translatePolyline
          (presentation.drawing.periodTranslation
            (Cell.sub first.offset second.offset))
          (presentation.incidenceRoute
            ⟨second.tripleIndex, color⟩)).reverse =
      (translatePolyline (presentation.drawing.periodTranslation translate)
        (translatePolyline
          (presentation.drawing.periodTranslation
            (Cell.sub first.offset second.offset))
          (presentation.incidenceRoute
            ⟨second.tripleIndex, color⟩))).reverse by
      simp [translatePolyline]]
  rw [translatePolyline_add_local]
  rw [periodTranslation_add]

/-- The source incidence tag is listed in every contracted edge's metadata. -/
theorem ContractedEdge.sourceTag_mem_incidenceTags
    (edge : ContractedEdge) : edge.sourceTag ∈ edge.incidenceTags := by
  cases edge <;> simp [ContractedEdge.incidenceTags,
    ContractedEdge.sourceTag]

/-- The target incidence tag of a through edge is listed in its metadata. -/
theorem ContractedEdge.targetTag_mem_incidenceTags_through
    (color : WireColor) (atom : Nat) (first second : Incidence) :
    (ContractedEdge.through color atom first second).targetTag ∈
      (ContractedEdge.through color atom first second).incidenceTags := by
  simp [ContractedEdge.incidenceTags, ContractedEdge.targetTag]

/-- The two incidence tags consumed by one through edge are distinct under
the degree promise. -/
theorem ContractedEdge.sourceTag_ne_targetTag_through
    (problem : PeriodicThreeDM)
    (degree : problem.DegreeTwoOrThree)
    {color : WireColor} {atom : Nat} {first second : Incidence}
    (edgeMember :
      ContractedEdge.through color atom first second ∈
        problem.contractedEdges) :
    (ContractedEdge.through color atom first second).sourceTag ≠
      (ContractedEdge.through color atom first second).targetTag := by
  have flattenedNodup := contractedIncidenceTags_nodup problem degree
  have localNodup :=
    (List.nodup_flatMap.mp flattenedNodup).1
      (ContractedEdge.through color atom first second) edgeMember
  simpa [contractedIncidenceTags, ContractedEdge.incidenceTags] using
    localNodup

/-- Distinct contracted source-edge occurrences give distinct source-piece
occurrences. -/
theorem ContractedEdge.sourcePieces_sourceDifferent
    (problem : PeriodicThreeDM)
    (degree : problem.DegreeTwoOrThree)
    {firstEdge secondEdge : ContractedEdge}
    (firstMember : firstEdge ∈ problem.contractedEdges)
    (secondMember : secondEdge ∈ problem.contractedEdges)
    (firstTranslate secondTranslate : Cell)
    (different :
      (firstEdge, firstTranslate) ≠ (secondEdge, secondTranslate)) :
    (firstEdge.sourcePiece firstTranslate).SourceOccurrenceDifferent
      (secondEdge.sourcePiece secondTranslate) := by
  intro equal
  have tagEqual : firstEdge.sourceTag = secondEdge.sourceTag :=
    congrArg Prod.fst equal
  have edgeEqual :=
    contractedEdges_eq_of_common_incidenceTag
      problem degree firstMember secondMember
      firstEdge.sourceTag_mem_incidenceTags
      (tagEqual ▸ secondEdge.sourceTag_mem_incidenceTags)
  subst secondEdge
  apply different
  have translatesEqual : firstTranslate = secondTranslate := by
    simpa [ContractedEdge.sourcePiece] using congrArg Prod.snd equal
  exact Prod.ext (by rfl) translatesEqual

/-- Source and target pieces of through edges are always distinct source
incidence occurrences, even before comparing their lattice shifts. -/
theorem ContractedEdge.sourcePiece_throughTargetPiece_sourceDifferent
    (problem : PeriodicThreeDM)
    (degree : problem.DegreeTwoOrThree)
    {firstEdge : ContractedEdge}
    {color : WireColor} {atom : Nat} {first second : Incidence}
    (firstMember : firstEdge ∈ problem.contractedEdges)
    (secondMember :
      ContractedEdge.through color atom first second ∈
        problem.contractedEdges)
    (firstTranslate secondTranslate : Cell) :
    (firstEdge.sourcePiece firstTranslate).SourceOccurrenceDifferent
      (ContractedEdge.throughTargetPiece
        color atom first second secondTranslate) := by
  intro equal
  have tagEqual : firstEdge.sourceTag =
      (ContractedEdge.through color atom first second).targetTag :=
    congrArg Prod.fst equal
  have edgeEqual :=
    contractedEdges_eq_of_common_incidenceTag
      problem degree firstMember secondMember
      firstEdge.sourceTag_mem_incidenceTags
      (tagEqual ▸
        ContractedEdge.targetTag_mem_incidenceTags_through
          color atom first second)
  subst firstEdge
  exact
    (ContractedEdge.sourceTag_ne_targetTag_through
      problem degree secondMember) tagEqual

/-- The symmetric target/source pairing is also a pair of distinct source
incidence occurrences. -/
theorem ContractedEdge.throughTargetPiece_sourcePiece_sourceDifferent
    (problem : PeriodicThreeDM)
    (degree : problem.DegreeTwoOrThree)
    {color : WireColor} {atom : Nat} {first second : Incidence}
    {secondEdge : ContractedEdge}
    (firstMember :
      ContractedEdge.through color atom first second ∈
        problem.contractedEdges)
    (secondMember : secondEdge ∈ problem.contractedEdges)
    (firstTranslate secondTranslate : Cell) :
    (ContractedEdge.throughTargetPiece
        color atom first second firstTranslate).SourceOccurrenceDifferent
      (secondEdge.sourcePiece secondTranslate) := by
  intro equal
  exact
    ContractedEdge.sourcePiece_throughTargetPiece_sourceDifferent
      problem degree secondMember firstMember secondTranslate firstTranslate
      equal.symm

/-- Distinct through-edge occurrences give distinct translated target-piece
occurrences. -/
theorem ContractedEdge.throughTargetPieces_sourceDifferent
    (problem : PeriodicThreeDM)
    (degree : problem.DegreeTwoOrThree)
    {firstColor secondColor : WireColor}
    {firstAtom secondAtom : Nat}
    {firstSource firstTarget secondSource secondTarget : Incidence}
    (firstMember :
      ContractedEdge.through firstColor firstAtom firstSource firstTarget ∈
        problem.contractedEdges)
    (secondMember :
      ContractedEdge.through secondColor secondAtom secondSource secondTarget ∈
        problem.contractedEdges)
    (firstTranslate secondTranslate : Cell)
    (different :
      (ContractedEdge.through firstColor firstAtom firstSource firstTarget,
          firstTranslate) ≠
        (ContractedEdge.through secondColor secondAtom secondSource secondTarget,
          secondTranslate)) :
    (ContractedEdge.throughTargetPiece
        firstColor firstAtom firstSource firstTarget firstTranslate)
        |>.SourceOccurrenceDifferent
      (ContractedEdge.throughTargetPiece
        secondColor secondAtom secondSource secondTarget secondTranslate) := by
  intro equal
  have tagEqual :
      (ContractedEdge.through firstColor firstAtom
        firstSource firstTarget).targetTag =
      (ContractedEdge.through secondColor secondAtom
        secondSource secondTarget).targetTag :=
    congrArg Prod.fst equal
  have edgeEqual :=
    contractedEdges_eq_of_common_incidenceTag
      problem degree firstMember secondMember
      (ContractedEdge.targetTag_mem_incidenceTags_through
        firstColor firstAtom firstSource firstTarget)
      (tagEqual ▸ ContractedEdge.targetTag_mem_incidenceTags_through
        secondColor secondAtom secondSource secondTarget)
  cases edgeEqual
  apply different
  have shiftsEqual := congrArg Prod.snd equal
  have translatesEqual : firstTranslate = secondTranslate :=
    Cell.add_left_injective
      (Cell.sub firstSource.offset firstTarget.offset) (by
        simpa [ContractedEdge.throughTargetPiece] using shiftsEqual)
  exact Prod.ext (by rfl) translatesEqual

private theorem eq_of_mem_of_mem_of_length_one
    {Item : Type*} {items : List Item} {first second : Item}
    (length : items.length = 1)
    (firstMember : first ∈ items) (secondMember : second ∈ items) :
    first = second := by
  rcases items with _ | ⟨head, tail⟩
  · simp at length
  rcases tail with _ | ⟨next, rest⟩
  · simp only [List.mem_singleton] at firstMember secondMember
    exact firstMember.trans secondMember.symm
  · simp at length

/-- The suppressed-element occurrence uniquely determines a through-edge
occurrence.  Thus distinct contracted occurrences have distinct splice
points. -/
theorem ContractedEdge.throughSpliceOccurrences_ne
    (problem : PeriodicThreeDM)
    {firstColor secondColor : WireColor}
    {firstAtom secondAtom : Nat}
    {firstSource firstTarget secondSource secondTarget : Incidence}
    (firstMember :
      ContractedEdge.through firstColor firstAtom firstSource firstTarget ∈
        problem.contractedEdges)
    (secondMember :
      ContractedEdge.through secondColor secondAtom secondSource secondTarget ∈
        problem.contractedEdges)
    (firstTranslate secondTranslate : Cell)
    (different :
      (ContractedEdge.through firstColor firstAtom firstSource firstTarget,
          firstTranslate) ≠
        (ContractedEdge.through secondColor secondAtom secondSource secondTarget,
          secondTranslate)) :
    ((PeriodicThreeDMVertex.element firstColor firstAtom),
        Cell.add firstSource.offset firstTranslate) ≠
      ((PeriodicThreeDMVertex.element secondColor secondAtom),
        Cell.add secondSource.offset secondTranslate) := by
  intro equal
  have verticesEqual := congrArg Prod.fst equal
  injection verticesEqual with colorEqual atomEqual
  subst secondColor
  subst secondAtom
  have firstLocal := contractedEdge_mem_own_element problem firstMember
  have secondLocal := contractedEdge_mem_own_element problem secondMember
  simp only [ContractedEdge.color, ContractedEdge.atom] at firstLocal
  simp only [ContractedEdge.color, ContractedEdge.atom] at secondLocal
  have firstDegree : problem.degree firstColor firstAtom = 2 := by
    have facts :=
      contractedEdge_incidence_members_of_mem problem firstMember
    simpa [ContractedEdge.color, ContractedEdge.atom,
      ContractedEdge.targetIsElement] using facts.2.2
  have edgeEqual :
      ContractedEdge.through firstColor firstAtom firstSource firstTarget =
        ContractedEdge.through firstColor firstAtom secondSource secondTarget :=
    eq_of_mem_of_mem_of_length_one
      (contractedEdgesForElement_length_of_degree_two
        problem firstColor firstAtom firstDegree)
      firstLocal secondLocal
  cases edgeEqual
  apply different
  have shiftsEqual := congrArg Prod.snd equal
  have translatesEqual : firstTranslate = secondTranslate :=
    Cell.add_left_injective firstSource.offset shiftsEqual
  exact Prod.ext (by rfl) translatesEqual

/-- A suppressed degree-two element occurrence cannot be the retained
degree-three endpoint of an emitted retained edge. -/
theorem ContractedEdge.throughSplice_ne_retainedFinish
    (problem : PeriodicThreeDM)
    {throughColor retainedColor : WireColor}
    {throughAtom retainedAtom : Nat}
    {first second incidence : Incidence}
    (throughMember :
      ContractedEdge.through throughColor throughAtom first second ∈
        problem.contractedEdges)
    (retainedMember :
      ContractedEdge.retained retainedColor retainedAtom incidence ∈
        problem.contractedEdges)
    (throughTranslate retainedTranslate : Cell) :
    ((PeriodicThreeDMVertex.element throughColor throughAtom),
        Cell.add first.offset throughTranslate) ≠
      ((PeriodicThreeDMVertex.element retainedColor retainedAtom),
        Cell.add incidence.offset retainedTranslate) := by
  intro equal
  have verticesEqual := congrArg Prod.fst equal
  injection verticesEqual with colorEqual atomEqual
  subst retainedColor
  subst retainedAtom
  have throughFacts :=
    contractedEdge_incidence_members_of_mem problem throughMember
  have retainedFacts :=
    contractedEdge_incidence_members_of_mem problem retainedMember
  have throughDegree : problem.degree throughColor throughAtom = 2 := by
    simpa [ContractedEdge.color, ContractedEdge.atom,
      ContractedEdge.targetIsElement] using throughFacts.2.2
  have retainedDegree : problem.degree throughColor throughAtom = 3 := by
    simpa [ContractedEdge.color, ContractedEdge.atom,
      ContractedEdge.targetIsElement] using retainedFacts.2.2
  omega

/-- A through-route occurrence and a retained-route occurrence satisfy
complete route separation: the suppressed splice is internal to only the
through route, while all remaining contacts are outer endpoints. -/
theorem PlanarPresentation.throughRouteOccurrence_avoid_retainedOccurrence
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (degree : problem.DegreeTwoOrThree)
    (separated : presentation.drawing.LiftedRoutesAvoidEachOther)
    {throughColor retainedColor : WireColor}
    {throughAtom retainedAtom : Nat}
    {first second incidence : Incidence}
    (throughMember :
      ContractedEdge.through throughColor throughAtom first second ∈
        problem.contractedEdges)
    (retainedMember :
      ContractedEdge.retained retainedColor retainedAtom incidence ∈
        problem.contractedEdges)
    (throughTranslate retainedTranslate : Cell) :
    RoutesAvoidEachOther
      (presentation.contractedEdgeRouteOccurrence
        (.through throughColor throughAtom first second)
        throughTranslate)
      (presentation.contractedEdgeRouteOccurrence
        (.retained retainedColor retainedAtom incidence)
        retainedTranslate) := by
  let sourcePiece :=
    (ContractedEdge.through throughColor throughAtom first second)
      |>.sourcePiece throughTranslate
  let targetPiece :=
    ContractedEdge.throughTargetPiece
      throughColor throughAtom first second throughTranslate
  let retainedPiece :=
    (ContractedEdge.retained retainedColor retainedAtom incidence)
      |>.sourcePiece retainedTranslate
  have sourcePieceMember :=
    ContractedEdge.sourcePiece_tag_mem
      problem throughMember throughTranslate
  have targetPieceMember :=
    ContractedEdge.throughTargetPiece_tag_mem
      problem throughMember throughTranslate
  have retainedTagMember :=
    ContractedEdge.sourcePiece_tag_mem
      problem retainedMember retainedTranslate
  have sourcePieceDifferent :
      sourcePiece.SourceOccurrenceDifferent retainedPiece := by
    exact ContractedEdge.sourcePieces_sourceDifferent
      problem degree throughMember retainedMember
      throughTranslate retainedTranslate (by simp)
  have targetPieceDifferent :
      targetPiece.SourceOccurrenceDifferent retainedPiece := by
    exact ContractedEdge.throughTargetPiece_sourcePiece_sourceDifferent
      problem degree throughMember retainedMember
      throughTranslate retainedTranslate
  have spliceNeRetainedStart :
      sourcePiece.finishOccurrence problem ≠
        retainedPiece.startOccurrence problem := by
    rw [show sourcePiece.finishOccurrence problem =
        ((.element throughColor throughAtom),
          Cell.add first.offset throughTranslate) by
      exact ContractedEdge.sourcePiece_finishOccurrence_through
        problem throughMember throughTranslate]
    rw [show retainedPiece.startOccurrence problem =
        ((.triple incidence.tripleIndex), retainedTranslate) by
      simpa [retainedPiece, ContractedEdge.toPeriodicEdge] using
        ContractedEdge.sourcePiece_startOccurrence
          problem retainedMember retainedTranslate]
    simp
  have spliceNeRetainedFinish :
      sourcePiece.finishOccurrence problem ≠
        retainedPiece.finishOccurrence problem := by
    rw [show sourcePiece.finishOccurrence problem =
        ((.element throughColor throughAtom),
          Cell.add first.offset throughTranslate) by
      exact ContractedEdge.sourcePiece_finishOccurrence_through
        problem throughMember throughTranslate]
    rw [show retainedPiece.finishOccurrence problem =
        ((.element retainedColor retainedAtom),
          Cell.add incidence.offset retainedTranslate) by
      exact ContractedEdge.sourcePiece_finishOccurrence_retained
        problem retainedMember retainedTranslate]
    exact ContractedEdge.throughSplice_ne_retainedFinish
      problem throughMember retainedMember
      throughTranslate retainedTranslate
  have targetPieceStartEq :
      targetPiece.startOccurrence problem =
        ((.element throughColor throughAtom),
          Cell.add first.offset throughTranslate) :=
    ContractedEdge.throughTargetPiece_startOccurrence
      problem throughMember throughTranslate
  have targetPieceStartNeRetainedStart :
      targetPiece.startOccurrence problem ≠
        retainedPiece.startOccurrence problem := by
    rw [targetPieceStartEq]
    rw [show retainedPiece.startOccurrence problem =
        ((.triple incidence.tripleIndex), retainedTranslate) by
      simpa [retainedPiece, ContractedEdge.toPeriodicEdge] using
        ContractedEdge.sourcePiece_startOccurrence
          problem retainedMember retainedTranslate]
    simp
  have targetPieceStartNeRetainedFinish :
      targetPiece.startOccurrence problem ≠
        retainedPiece.finishOccurrence problem := by
    rw [targetPieceStartEq]
    rw [show retainedPiece.finishOccurrence problem =
        ((.element retainedColor retainedAtom),
          Cell.add incidence.offset retainedTranslate) by
      exact ContractedEdge.sourcePiece_finishOccurrence_retained
        problem retainedMember retainedTranslate]
    exact ContractedEdge.throughSplice_ne_retainedFinish
      problem throughMember retainedMember
      throughTranslate retainedTranslate
  have sourcePieceAvoid :=
    presentation.contractedRoutePieces_avoidEachOther separated
      sourcePiece retainedPiece sourcePieceMember retainedTagMember sourcePieceDifferent
  have targetPieceAvoid :=
    presentation.contractedRoutePieces_avoidEachOther separated
      targetPiece retainedPiece targetPieceMember retainedTagMember targetPieceDifferent
  have sourcePieceContacts :=
    presentation.contractedRoutePieces_meetOnlyAtFirstHead separated
      sourcePiece retainedPiece sourcePieceMember retainedTagMember sourcePieceDifferent
      spliceNeRetainedStart spliceNeRetainedFinish
  have targetPieceContacts :=
    presentation.contractedRoutePieces_meetOnlyAtFirstTail separated
      targetPiece retainedPiece targetPieceMember retainedTagMember targetPieceDifferent
      targetPieceStartNeRetainedStart targetPieceStartNeRetainedFinish
  let middle :=
    Cell.add
      (presentation.drawing.vertexPosition problem.incidenceGraph
        (.element throughColor throughAtom))
      (presentation.drawing.periodTranslation
        (Cell.add first.offset throughTranslate))
  have sourcePieceEndpoints :=
    ContractedRoutePiece.route_endpoints
      presentation sourcePiece sourcePieceMember
  have targetPieceEndpoints :=
    ContractedRoutePiece.route_endpoints
      presentation targetPiece targetPieceMember
  have entrance : (sourcePiece.route presentation).getLast? = some middle := by
    rw [sourcePieceEndpoints.2]
    rw [show sourcePiece.finishOccurrence problem =
        ((.element throughColor throughAtom),
          Cell.add first.offset throughTranslate) by
      exact ContractedEdge.sourcePiece_finishOccurrence_through
        problem throughMember throughTranslate]
  have targetPieceHead : (targetPiece.route presentation).head? = some middle := by
    rw [targetPieceEndpoints.1, targetPieceStartEq]
  rw [presentation.contractedEdgeRouteOccurrence_through,
    presentation.contractedEdgeRouteOccurrence_retained]
  exact RoutesAvoidEachOther.join_left_of_outer_endpoint_contacts
    sourcePieceAvoid sourcePieceContacts targetPieceAvoid targetPieceContacts
      entrance targetPieceHead

/-- Two distinct through-route occurrences remain completely separated
after both endpoint joins; their suppressed splice occurrences are distinct,
so all surviving contacts are outer contracted-edge endpoints. -/
theorem PlanarPresentation.throughRouteOccurrences_avoidEachOther
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (degree : problem.DegreeTwoOrThree)
    (separated : presentation.drawing.LiftedRoutesAvoidEachOther)
    {firstColor secondColor : WireColor}
    {firstAtom secondAtom : Nat}
    {firstSource firstTarget secondSource secondTarget : Incidence}
    (firstMember :
      ContractedEdge.through firstColor firstAtom firstSource firstTarget ∈
        problem.contractedEdges)
    (secondMember :
      ContractedEdge.through secondColor secondAtom secondSource secondTarget ∈
        problem.contractedEdges)
    (firstTranslate secondTranslate : Cell)
    (different :
      (ContractedEdge.through firstColor firstAtom firstSource firstTarget,
          firstTranslate) ≠
        (ContractedEdge.through secondColor secondAtom secondSource secondTarget,
          secondTranslate)) :
    RoutesAvoidEachOther
      (presentation.contractedEdgeRouteOccurrence
        (.through firstColor firstAtom firstSource firstTarget)
        firstTranslate)
      (presentation.contractedEdgeRouteOccurrence
        (.through secondColor secondAtom secondSource secondTarget)
        secondTranslate) := by
  let firstSourcePiece :=
    (ContractedEdge.through firstColor firstAtom firstSource firstTarget)
      |>.sourcePiece firstTranslate
  let firstTargetPiece :=
    ContractedEdge.throughTargetPiece
      firstColor firstAtom firstSource firstTarget firstTranslate
  let secondSourcePiece :=
    (ContractedEdge.through secondColor secondAtom secondSource secondTarget)
      |>.sourcePiece secondTranslate
  let secondTargetPiece :=
    ContractedEdge.throughTargetPiece
      secondColor secondAtom secondSource secondTarget secondTranslate
  have firstSourceMember :=
    ContractedEdge.sourcePiece_tag_mem problem firstMember firstTranslate
  have firstTargetMember :=
    ContractedEdge.throughTargetPiece_tag_mem
      problem firstMember firstTranslate
  have secondSourceMember :=
    ContractedEdge.sourcePiece_tag_mem problem secondMember secondTranslate
  have secondTargetMember :=
    ContractedEdge.throughTargetPiece_tag_mem
      problem secondMember secondTranslate
  have sourceSourceDifferent :
      firstSourcePiece.SourceOccurrenceDifferent secondSourcePiece :=
    ContractedEdge.sourcePieces_sourceDifferent
      problem degree firstMember secondMember
      firstTranslate secondTranslate different
  have sourceTargetDifferent :
      firstSourcePiece.SourceOccurrenceDifferent secondTargetPiece :=
    ContractedEdge.sourcePiece_throughTargetPiece_sourceDifferent
      problem degree firstMember secondMember
      firstTranslate secondTranslate
  have targetSourceDifferent :
      firstTargetPiece.SourceOccurrenceDifferent secondSourcePiece :=
    ContractedEdge.throughTargetPiece_sourcePiece_sourceDifferent
      problem degree firstMember secondMember
      firstTranslate secondTranslate
  have targetTargetDifferent :
      firstTargetPiece.SourceOccurrenceDifferent secondTargetPiece :=
    ContractedEdge.throughTargetPieces_sourceDifferent
      problem degree firstMember secondMember
      firstTranslate secondTranslate different
  have firstSourceStartEq :
      firstSourcePiece.startOccurrence problem =
        ((.triple firstSource.tripleIndex), firstTranslate) := by
    simpa [firstSourcePiece, ContractedEdge.toPeriodicEdge] using
      ContractedEdge.sourcePiece_startOccurrence
        problem firstMember firstTranslate
  have firstSourceFinishEq :
      firstSourcePiece.finishOccurrence problem =
        ((.element firstColor firstAtom),
          Cell.add firstSource.offset firstTranslate) :=
    ContractedEdge.sourcePiece_finishOccurrence_through
      problem firstMember firstTranslate
  have firstTargetStartEq :
      firstTargetPiece.startOccurrence problem =
        ((.element firstColor firstAtom),
          Cell.add firstSource.offset firstTranslate) :=
    ContractedEdge.throughTargetPiece_startOccurrence
      problem firstMember firstTranslate
  have firstTargetFinishEq :
      firstTargetPiece.finishOccurrence problem =
        ((.triple firstTarget.tripleIndex),
          Cell.add (Cell.sub firstSource.offset firstTarget.offset)
            firstTranslate) :=
    ContractedEdge.throughTargetPiece_finishOccurrence
      problem firstMember firstTranslate
  have secondSourceStartEq :
      secondSourcePiece.startOccurrence problem =
        ((.triple secondSource.tripleIndex), secondTranslate) := by
    simpa [secondSourcePiece, ContractedEdge.toPeriodicEdge] using
      ContractedEdge.sourcePiece_startOccurrence
        problem secondMember secondTranslate
  have secondSourceFinishEq :
      secondSourcePiece.finishOccurrence problem =
        ((.element secondColor secondAtom),
          Cell.add secondSource.offset secondTranslate) :=
    ContractedEdge.sourcePiece_finishOccurrence_through
      problem secondMember secondTranslate
  have secondTargetStartEq :
      secondTargetPiece.startOccurrence problem =
        ((.element secondColor secondAtom),
          Cell.add secondSource.offset secondTranslate) :=
    ContractedEdge.throughTargetPiece_startOccurrence
      problem secondMember secondTranslate
  have secondTargetFinishEq :
      secondTargetPiece.finishOccurrence problem =
        ((.triple secondTarget.tripleIndex),
          Cell.add (Cell.sub secondSource.offset secondTarget.offset)
            secondTranslate) :=
    ContractedEdge.throughTargetPiece_finishOccurrence
      problem secondMember secondTranslate
  have splicesNe :
      firstSourcePiece.finishOccurrence problem ≠
        secondSourcePiece.finishOccurrence problem := by
    rw [firstSourceFinishEq, secondSourceFinishEq]
    exact ContractedEdge.throughSpliceOccurrences_ne
      problem firstMember secondMember
      firstTranslate secondTranslate different
  have prefixesAvoid :=
    presentation.contractedRoutePieces_avoidEachOther separated
      firstSourcePiece secondSourcePiece
      firstSourceMember secondSourceMember sourceSourceDifferent
  have prefixContacts :=
    presentation.contractedRoutePieces_meetOnlyAtHeads separated
      firstSourcePiece secondSourcePiece
      firstSourceMember secondSourceMember sourceSourceDifferent
      (by rw [firstSourceStartEq, secondSourceFinishEq]; simp)
      (by rw [firstSourceFinishEq, secondSourceStartEq]; simp)
      splicesNe
  have firstSourceSecondTargetAvoid :=
    presentation.contractedRoutePieces_avoidEachOther separated
      firstSourcePiece secondTargetPiece
      firstSourceMember secondTargetMember sourceTargetDifferent
  have firstSourceSecondTargetContacts :=
    presentation.contractedRoutePieces_meetOnlyAtFirstHeadSecondTail separated
      firstSourcePiece secondTargetPiece
      firstSourceMember secondTargetMember sourceTargetDifferent
      (by rw [firstSourceStartEq, secondTargetStartEq]; simp)
      (by
        rw [firstSourceFinishEq, secondTargetStartEq]
        exact ContractedEdge.throughSpliceOccurrences_ne
          problem firstMember secondMember
          firstTranslate secondTranslate different)
      (by rw [firstSourceFinishEq, secondTargetFinishEq]; simp)
  have firstTargetSecondSourceAvoid :=
    presentation.contractedRoutePieces_avoidEachOther separated
      firstTargetPiece secondSourcePiece
      firstTargetMember secondSourceMember targetSourceDifferent
  have secondSourceFirstTargetContacts :=
    presentation.contractedRoutePieces_meetOnlyAtFirstHeadSecondTail separated
      secondSourcePiece firstTargetPiece
      secondSourceMember firstTargetMember
      (ContractedEdge.sourcePiece_throughTargetPiece_sourceDifferent
        problem degree secondMember firstMember
        secondTranslate firstTranslate)
      (by rw [secondSourceStartEq, firstTargetStartEq]; simp)
      (by
        rw [secondSourceFinishEq, firstTargetStartEq]
        exact (ContractedEdge.throughSpliceOccurrences_ne
          problem firstMember secondMember
          firstTranslate secondTranslate different).symm)
      (by rw [secondSourceFinishEq, firstTargetFinishEq]; simp)
  have suffixesAvoid :=
    presentation.contractedRoutePieces_avoidEachOther separated
      firstTargetPiece secondTargetPiece
      firstTargetMember secondTargetMember targetTargetDifferent
  have suffixContacts :=
    presentation.contractedRoutePieces_meetOnlyAtTails separated
      firstTargetPiece secondTargetPiece
      firstTargetMember secondTargetMember targetTargetDifferent
      (by
        rw [firstTargetStartEq, secondTargetStartEq]
        exact ContractedEdge.throughSpliceOccurrences_ne
          problem firstMember secondMember
          firstTranslate secondTranslate different)
      (by rw [firstTargetStartEq, secondTargetFinishEq]; simp)
      (by rw [firstTargetFinishEq, secondTargetStartEq]; simp)
  let firstMiddle :=
    Cell.add
      (presentation.drawing.vertexPosition problem.incidenceGraph
        (.element firstColor firstAtom))
      (presentation.drawing.periodTranslation
        (Cell.add firstSource.offset firstTranslate))
  let secondMiddle :=
    Cell.add
      (presentation.drawing.vertexPosition problem.incidenceGraph
        (.element secondColor secondAtom))
      (presentation.drawing.periodTranslation
        (Cell.add secondSource.offset secondTranslate))
  have firstSourceEndpoints :=
    ContractedRoutePiece.route_endpoints
      presentation firstSourcePiece firstSourceMember
  have firstTargetEndpoints :=
    ContractedRoutePiece.route_endpoints
      presentation firstTargetPiece firstTargetMember
  have secondSourceEndpoints :=
    ContractedRoutePiece.route_endpoints
      presentation secondSourcePiece secondSourceMember
  have secondTargetEndpoints :=
    ContractedRoutePiece.route_endpoints
      presentation secondTargetPiece secondTargetMember
  have firstEntrance :
      (firstSourcePiece.route presentation).getLast? =
        some firstMiddle := by
    rw [firstSourceEndpoints.2, firstSourceFinishEq]
  have firstTargetHead :
      (firstTargetPiece.route presentation).head? =
        some firstMiddle := by
    rw [firstTargetEndpoints.1, firstTargetStartEq]
  have secondEntrance :
      (secondSourcePiece.route presentation).getLast? =
        some secondMiddle := by
    rw [secondSourceEndpoints.2, secondSourceFinishEq]
  have secondTargetHead :
      (secondTargetPiece.route presentation).head? =
        some secondMiddle := by
    rw [secondTargetEndpoints.1, secondTargetStartEq]
  rw [presentation.contractedEdgeRouteOccurrence_through,
    presentation.contractedEdgeRouteOccurrence_through]
  exact RoutesAvoidEachOther.join_both_of_outer_endpoint_contacts
    prefixesAvoid prefixContacts
    firstSourceSecondTargetAvoid firstSourceSecondTargetContacts
    firstTargetSecondSourceAvoid secondSourceFirstTargetContacts
    suffixesAvoid suffixContacts
    firstEntrance firstTargetHead secondEntrance secondTargetHead

/-- Every pair of distinct contracted edge occurrences satisfies complete
route separation, by the retained/through case split. -/
theorem PlanarPresentation.contractedEdgeRouteOccurrences_avoidEachOther
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (degree : problem.DegreeTwoOrThree)
    (separated : presentation.drawing.LiftedRoutesAvoidEachOther)
    {firstEdge secondEdge : ContractedEdge}
    (firstMember : firstEdge ∈ problem.contractedEdges)
    (secondMember : secondEdge ∈ problem.contractedEdges)
    (firstTranslate secondTranslate : Cell)
    (different :
      (firstEdge, firstTranslate) ≠
        (secondEdge, secondTranslate)) :
    RoutesAvoidEachOther
      (presentation.contractedEdgeRouteOccurrence
        firstEdge firstTranslate)
      (presentation.contractedEdgeRouteOccurrence
        secondEdge secondTranslate) := by
  cases firstEdge with
  | retained firstColor firstAtom firstIncidence =>
      cases secondEdge with
      | retained secondColor secondAtom secondIncidence =>
          rw [presentation.contractedEdgeRouteOccurrence_retained,
            presentation.contractedEdgeRouteOccurrence_retained]
          apply presentation.contractedRoutePieces_avoidEachOther separated
          · exact ContractedEdge.sourcePiece_tag_mem
              problem firstMember firstTranslate
          · exact ContractedEdge.sourcePiece_tag_mem
              problem secondMember secondTranslate
          · exact ContractedEdge.sourcePieces_sourceDifferent
              problem degree firstMember secondMember
              firstTranslate secondTranslate different
      | through secondColor secondAtom secondSource secondTarget =>
          exact routesAvoidEachOther_comm
            (presentation.throughRouteOccurrence_avoid_retainedOccurrence
              degree separated secondMember firstMember
              secondTranslate firstTranslate)
  | through firstColor firstAtom firstSource firstTarget =>
      cases secondEdge with
      | retained secondColor secondAtom secondIncidence =>
          exact
            presentation.throughRouteOccurrence_avoid_retainedOccurrence
              degree separated firstMember secondMember
              firstTranslate secondTranslate
      | through secondColor secondAtom secondSource secondTarget =>
          exact presentation.throughRouteOccurrences_avoidEachOther
            degree separated firstMember secondMember
            firstTranslate secondTranslate different

/-- A stored contracted route and its list index recover the contracted edge
at the same index. -/
theorem PlanarPresentation.contractedDrawing_route_has_edge
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    {taggedRoute : List Cell × Nat}
    (member : taggedRoute ∈
      presentation.contractedDrawing.edgeRoutes.zipIdx) :
    ∃ edge : ContractedEdge,
      (edge, taggedRoute.2) ∈ problem.contractedEdges.zipIdx ∧
        taggedRoute.1 = presentation.contractedEdgeRoute edge := by
  have routeIndexLt := (List.mem_zipIdx' member).1
  have edgeIndexLt : taggedRoute.2 < problem.contractedEdges.length := by
    simpa [PlanarPresentation.contractedDrawing] using routeIndexLt
  let edge := problem.contractedEdges[taggedRoute.2]'edgeIndexLt
  have edgeMember :
      (edge, taggedRoute.2) ∈ problem.contractedEdges.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?, List.getElem?_eq_some_iff]
    exact ⟨edgeIndexLt, rfl⟩
  refine ⟨edge, edgeMember, ?_⟩
  have routeAt :
      presentation.contractedDrawing.edgeRoute taggedRoute.2 =
        taggedRoute.1 := by
    unfold PeriodicGridDrawing.edgeRoute
    rw [List.getD_eq_getElem _ _ routeIndexLt]
    exact (List.mem_zipIdx' member).2.symm
  exact routeAt.symm.trans
    (presentation.contractedDrawing_edgeRoute edgeMember)

/-- Complete lifted route separation survives degree-two contraction. -/
theorem PlanarPresentation.contractedDrawing_liftedRoutesAvoidEachOther
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (degree : problem.DegreeTwoOrThree)
    (separated : presentation.drawing.LiftedRoutesAvoidEachOther) :
    presentation.contractedDrawing.LiftedRoutesAvoidEachOther := by
  intro first firstMember second secondMember
    firstTranslate secondTranslate indicesDifferent
  rcases presentation.contractedDrawing_route_has_edge firstMember with
    ⟨firstEdge, firstEdgeMember, firstRouteEq⟩
  rcases presentation.contractedDrawing_route_has_edge secondMember with
    ⟨secondEdge, secondEdgeMember, secondRouteEq⟩
  have edgeOccurrencesDifferent :
      (firstEdge, firstTranslate) ≠
        (secondEdge, secondTranslate) := by
    intro equal
    apply indicesDifferent
    have edgesEqual : firstEdge = secondEdge :=
      congrArg Prod.fst equal
    have taggedEdgesEqual :=
      tagged_eq_of_mem_zipIdx_of_fst_eq_of_nodup
        (contractedEdges_nodup problem degree)
        firstEdgeMember secondEdgeMember edgesEqual
    have edgeIndicesEqual : first.2 = second.2 :=
      congrArg (fun tagged : ContractedEdge × Nat => tagged.2)
        taggedEdgesEqual
    have translatesEqual : firstTranslate = secondTranslate :=
      congrArg (fun occurrence : ContractedEdge × Cell => occurrence.2)
        equal
    exact Prod.ext edgeIndicesEqual translatesEqual
  have avoids :=
    presentation.contractedEdgeRouteOccurrences_avoidEachOther
      degree separated
      (List.fst_mem_of_mem_zipIdx firstEdgeMember)
      (List.fst_mem_of_mem_zipIdx secondEdgeMember)
      firstTranslate secondTranslate edgeOccurrencesDifferent
  change RoutesAvoidEachOther
    (translatePolyline
      (presentation.contractedDrawing.periodTranslation firstTranslate)
      first.1)
    (translatePolyline
      (presentation.contractedDrawing.periodTranslation secondTranslate)
      second.1)
  rw [firstRouteEq, secondRouteEq]
  rw [show presentation.contractedDrawing.periodTranslation firstTranslate =
        presentation.drawing.periodTranslation firstTranslate by rfl,
    show presentation.contractedDrawing.periodTranslation secondTranslate =
        presentation.drawing.periodTranslation secondTranslate by rfl]
  exact avoids

/-- Optional reversal and lattice translation preserve simplicity of a
source incidence-route piece. -/
theorem ContractedRoutePiece.route_isSimple
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (piece : ContractedRoutePiece)
    (tagMember : piece.tag ∈ problem.incidenceTags)
    (sourceSimple :
      ∀ route ∈ presentation.drawing.edgeRoutes,
        LocalIncidenceDrawing.RouteIsSimple route) :
    LocalIncidenceDrawing.RouteIsSimple (piece.route presentation) := by
  have baseSimple := sourceSimple
    (presentation.incidenceRoute piece.tag)
    (List.fst_mem_of_mem_zipIdx
      (presentation.incidenceRoute_zipIdx_mem tagMember))
  have translatedSimple :=
    routeIsSimple_translate baseSimple
      (presentation.drawing.periodTranslation piece.latticeShift)
  cases reversed : piece.reversed
  · simpa [ContractedRoutePiece.route,
      PlanarPresentation.incidenceRouteOccurrence, translatePolyline,
      reversed] using translatedSimple
  · simpa [ContractedRoutePiece.route,
      PlanarPresentation.incidenceRouteOccurrence, translatePolyline,
      reversed] using translatedSimple.reverse

/-- The zero lattice occurrence of a contracted route is its stored finite
representative. -/
theorem PlanarPresentation.contractedEdgeRouteOccurrence_zero
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (edge : ContractedEdge) :
    presentation.contractedEdgeRouteOccurrence edge (0, 0) =
      presentation.contractedEdgeRoute edge := by
  unfold PlanarPresentation.contractedEdgeRouteOccurrence
    translatePolyline
  induction presentation.contractedEdgeRoute edge with
  | nil => rfl
  | cons point points induction =>
      simp only [List.map_cons]
      rw [induction]
      congr 1
      apply Prod.ext <;>
        simp [PeriodicGridDrawing.periodTranslation,
          Cell.scale, Cell.add]

/-- Every contracted route is simple when the original stored incidence
routes are simple and their lifted occurrences satisfy complete separation. -/
theorem PlanarPresentation.contractedEdgeRoute_isSimple
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (degree : problem.DegreeTwoOrThree)
    (separated : presentation.drawing.LiftedRoutesAvoidEachOther)
    (sourceSimple :
      ∀ route ∈ presentation.drawing.edgeRoutes,
        LocalIncidenceDrawing.RouteIsSimple route)
    {edge : ContractedEdge}
    (edgeMember : edge ∈ problem.contractedEdges) :
    LocalIncidenceDrawing.RouteIsSimple
      (presentation.contractedEdgeRoute edge) := by
  cases edge with
  | retained color atom incidence =>
      let piece :=
        (ContractedEdge.retained color atom incidence)
          |>.sourcePiece (0, 0)
      have pieceMember := ContractedEdge.sourcePiece_tag_mem
        problem edgeMember (0, 0)
      have pieceSimple :=
        ContractedRoutePiece.route_isSimple
          presentation piece pieceMember sourceSimple
      rw [← presentation.contractedEdgeRouteOccurrence_retained] at pieceSimple
      rw [presentation.contractedEdgeRouteOccurrence_zero] at pieceSimple
      exact pieceSimple
  | through color atom first second =>
      let sourcePiece :=
        (ContractedEdge.through color atom first second)
          |>.sourcePiece (0, 0)
      let targetPiece :=
        ContractedEdge.throughTargetPiece
          color atom first second (0, 0)
      have sourcePieceMember := ContractedEdge.sourcePiece_tag_mem
        problem edgeMember (0, 0)
      have targetPieceMember :=
        ContractedEdge.throughTargetPiece_tag_mem
          problem edgeMember (0, 0)
      have sourcePieceSimple :=
        ContractedRoutePiece.route_isSimple
          presentation sourcePiece sourcePieceMember sourceSimple
      have targetPieceSimple :=
        ContractedRoutePiece.route_isSimple
          presentation targetPiece targetPieceMember sourceSimple
      have sourceTargetDifferent :
          sourcePiece.SourceOccurrenceDifferent targetPiece :=
        ContractedEdge.sourcePiece_throughTargetPiece_sourceDifferent
          problem degree edgeMember edgeMember (0, 0) (0, 0)
      have sourceTargetAvoid :=
        presentation.contractedRoutePieces_avoidEachOther separated
          sourcePiece targetPiece sourcePieceMember targetPieceMember
          sourceTargetDifferent
      have sourceStartEq :
          sourcePiece.startOccurrence problem =
            ((.triple first.tripleIndex), (0, 0)) := by
        simpa [sourcePiece, ContractedEdge.toPeriodicEdge] using
          ContractedEdge.sourcePiece_startOccurrence
            problem edgeMember (0, 0)
      have sourceFinishEq :
          sourcePiece.finishOccurrence problem =
            ((.element color atom), Cell.add first.offset (0, 0)) :=
        ContractedEdge.sourcePiece_finishOccurrence_through
          problem edgeMember (0, 0)
      have targetStartEq :
          targetPiece.startOccurrence problem =
            ((.element color atom), Cell.add first.offset (0, 0)) :=
        ContractedEdge.throughTargetPiece_startOccurrence
          problem edgeMember (0, 0)
      have targetFinishEq :
          targetPiece.finishOccurrence problem =
            ((.triple second.tripleIndex),
              Cell.add (Cell.sub first.offset second.offset) (0, 0)) :=
        ContractedEdge.throughTargetPiece_finishOccurrence
          problem edgeMember (0, 0)
      have endpointTagsDifferent :=
        ContractedEdge.sourceTag_ne_targetTag_through
          problem degree edgeMember
      have tripleIndicesDifferent :
          first.tripleIndex ≠ second.tripleIndex := by
        intro equal
        apply endpointTagsDifferent
        simp [ContractedEdge.sourceTag, ContractedEdge.targetTag,
          equal]
      have sourceStartNeTargetFinish :
          sourcePiece.startOccurrence problem ≠
            targetPiece.finishOccurrence problem := by
        rw [sourceStartEq, targetFinishEq]
        intro equal
        have verticesEqual := congrArg Prod.fst equal
        injection verticesEqual with indicesEqual
        exact tripleIndicesDifferent indicesEqual
      have contacts :=
        presentation.contractedRoutePieces_meetOnlyAtFirstTail separated
          sourcePiece targetPiece sourcePieceMember targetPieceMember
          sourceTargetDifferent
          (by rw [sourceStartEq, targetStartEq]; simp)
          sourceStartNeTargetFinish
      let middle :=
        Cell.add
          (presentation.drawing.vertexPosition problem.incidenceGraph
            (.element color atom))
          (presentation.drawing.periodTranslation
            (Cell.add first.offset (0, 0)))
      have sourceEndpoints :=
        ContractedRoutePiece.route_endpoints
          presentation sourcePiece sourcePieceMember
      have targetEndpoints :=
        ContractedRoutePiece.route_endpoints
          presentation targetPiece targetPieceMember
      have entrance :
          (sourcePiece.route presentation).getLast? = some middle := by
        rw [sourceEndpoints.2, sourceFinishEq]
      have targetHead :
          (targetPiece.route presentation).head? = some middle := by
        rw [targetEndpoints.1, targetStartEq]
      have onlyCommon :
          ∀ point,
            point ∈ sourcePiece.route presentation →
            point ∈ targetPiece.route presentation →
            point = middle := by
        intro point sourceMember targetMember
        have atTail := contacts point sourceMember point targetMember rfl
        exact Option.some.inj (atTail.1.symm.trans entrance)
      have joinedSimple :=
        LocalIncidenceDrawing.RouteIsSimple.joinAtEndpoint_of_only_common
          sourcePieceSimple targetPieceSimple sourceTargetAvoid
          entrance targetHead onlyCommon
      rw [← presentation.contractedEdgeRouteOccurrence_through] at joinedSimple
      rw [presentation.contractedEdgeRouteOccurrence_zero] at joinedSimple
      exact joinedSimple

/-- Consequently every route stored in the contracted drawing is simple. -/
theorem PlanarPresentation.contractedDrawing_routesSimple
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (degree : problem.DegreeTwoOrThree)
    (separated : presentation.drawing.LiftedRoutesAvoidEachOther)
    (sourceSimple :
      ∀ route ∈ presentation.drawing.edgeRoutes,
        LocalIncidenceDrawing.RouteIsSimple route) :
    ∀ route ∈ presentation.contractedDrawing.edgeRoutes,
      LocalIncidenceDrawing.RouteIsSimple route := by
  intro route routeMember
  rcases List.mem_iff_get.mp routeMember with ⟨index, routeAt⟩
  have taggedMember :
      (route, index.val) ∈
        presentation.contractedDrawing.edgeRoutes.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?, List.getElem?_eq_some_iff]
    exact ⟨index.isLt, routeAt⟩
  rcases presentation.contractedDrawing_route_has_edge taggedMember with
    ⟨edge, edgeMember, routeEq⟩
  change route = presentation.contractedEdgeRoute edge at routeEq
  rw [routeEq]
  exact presentation.contractedEdgeRoute_isSimple
    degree separated sourceSimple
      (List.fst_mem_of_mem_zipIdx edgeMember)

/-- Degree-two contraction preserves the drawing-level endpoint-contact
certificate. -/
theorem PlanarPresentation.contractedDrawing_routePointsMeetOnlyAtEndpoints
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (degree : problem.DegreeTwoOrThree)
    (separated : presentation.drawing.LiftedRoutesAvoidEachOther)
    (sourceSimple :
      ∀ route ∈ presentation.drawing.edgeRoutes,
        LocalIncidenceDrawing.RouteIsSimple route) :
    presentation.contractedDrawing.RoutePointsMeetOnlyAtEndpoints :=
  PeriodicGridDrawing.routePointsMeetOnlyAtEndpoints_of_liftedRoutesAvoidEachOther
    (presentation.contractedDrawing_liftedRoutesAvoidEachOther
      degree separated)
    (presentation.contractedDrawing_routesSimple
      degree separated sourceSimple)

end PeriodicThreeDM

end LeanTrominoes
