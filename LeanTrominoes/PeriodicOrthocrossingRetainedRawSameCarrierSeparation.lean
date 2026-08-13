/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierPairOrder
import LeanTrominoes.PeriodicOrthocrossingRetainedRawCarrierGeometry

/-!
# Separation of raw retained lenses on one carrier

Raw retained links are consecutive pairs in a strictly ordered retained
carrier chain.  Thus distinct raw links on one physical carrier are axially
ordered.  Nonadjacent links have disjoint narrow rectangles, while adjacent
links have complementary endpoint boundaries and can meet only at advertised
route endpoints.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 800000

/-- Distinct raw retained links with the same carrier key occur in one of
the two nonoverlapping axial orders. -/
theorem retainedDrawingCompleteCarrierLinksRaw_same_key_orderCoordinate
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {firstLink secondLink : EqualityLink CarrierNode}
    (firstMem :
      firstLink ∈ retainedDrawingCompleteCarrierLinksRaw graph)
    (secondMem :
      secondLink ∈ retainedDrawingCompleteCarrierLinksRaw graph)
    (different : firstLink ≠ secondLink)
    (sameKey :
      firstLink.first.carrierKey =
        secondLink.first.carrierKey) :
    firstLink.second.orderCoordinate graph ≤
        secondLink.first.orderCoordinate graph ∨
      secondLink.second.orderCoordinate graph ≤
        firstLink.first.orderCoordinate graph := by
  rcases List.mem_flatMap.mp firstMem with
    ⟨firstKey, _firstKeyMem, firstLinkMem⟩
  rcases List.mem_flatMap.mp secondMem with
    ⟨secondKey, _secondKeyMem, secondLinkMem⟩
  have firstCommon :=
    retainedCompleteCarrierLinks_common_key
      graph firstKey firstLinkMem
  have secondCommon :=
    retainedCompleteCarrierLinks_common_key
      graph secondKey secondLinkMem
  have keyEqual : firstKey = secondKey :=
    firstCommon.1.symm.trans
      (sameKey.trans secondCommon.1)
  subst secondKey
  rcases List.mem_map.mp firstLinkMem with
    ⟨firstPair, firstPairMem, firstLinkEqual⟩
  rcases List.mem_map.mp secondLinkMem with
    ⟨secondPair, secondPairMem, secondLinkEqual⟩
  subst firstLink
  subst secondLink
  have firstPairRaw :=
    (List.mem_filter.mp firstPairMem).1
  have secondPairRaw :=
    (List.mem_filter.mp secondPairMem).1
  have pairDifferent : firstPair ≠ secondPair := by
    intro pairEqual
    subst secondPair
    exact different rfl
  simpa [carrierNodePairLink] using
    List.consecutivePairs_nonoverlap_of_ne_of_pairwise_lt
      (CarrierNode.orderCoordinate graph)
      (retainedCompleteCarrierNodes_pairwise_orderCoordinate_lt
        wellFormed degree isLocal firstKey)
      firstPairRaw secondPairRaw pairDifferent

/-- At a shared carrier node, the exterior of the later raw link's first
boundary lies inside the earlier raw link's second boundary. -/
theorem
    retainedDrawingCompleteCarrierLinksRaw_firstExterior_insideSecondBoundary_of_shared
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {earlier later : EqualityLink CarrierNode}
    (earlierMem :
      earlier ∈ retainedDrawingCompleteCarrierLinksRaw graph)
    (laterMem :
      later ∈ retainedDrawingCompleteCarrierLinksRaw graph)
    (shared : earlier.second = later.first)
    (point : Cell)
    (outside :
      (EqualityLink.firstCarrierPort
        (CarrierNode.position graph) later).OutsideCarrierBoundaryAt
          (EqualityLink.firstCarrierMacroOrigin
            (CarrierNode.position graph) later)
          point) :
    (EqualityLink.secondCarrierPort
      (CarrierNode.position graph) earlier).InsideCarrierBoundaryAt
        (EqualityLink.secondCarrierMacroOrigin
          (CarrierNode.position graph) earlier)
        point := by
  have earlierAxis :=
    retainedDrawingCompleteCarrierLinkRaw_first_isHorizontal_iff_second
      wellFormed degree isLocal earlierMem
  have laterAxis :=
    retainedDrawingCompleteCarrierLinkRaw_first_isHorizontal_iff_second
      wellFormed degree isLocal laterMem
  have earlierPort :=
    retainedDrawingCompleteCarrierLinkRaw_secondCarrierPort_eq_axis
      wellFormed degree isLocal earlierMem
  have laterPort :=
    retainedDrawingCompleteCarrierLinkRaw_firstCarrierPort_eq_axis
      wellFormed degree isLocal laterMem
  have earlierContact :=
    EqualityLink.add_secondCarrierMacroOrigin_portPosition
      (retainedDrawingCompleteCarrierLinkRaw_lensGeometry
        wellFormed degree isLocal earlierMem)
  have laterContact :=
    EqualityLink.add_firstCarrierMacroOrigin_portPosition
      (CarrierNode.position graph) later
  by_cases horizontal : earlier.first.isHorizontal = true
  · have earlierSecondHorizontal := earlierAxis.mp horizontal
    have laterFirstHorizontal :
        later.first.isHorizontal = true := by
      rw [← shared]
      exact earlierSecondHorizontal
    rw [if_pos horizontal] at earlierPort
    rw [if_pos laterFirstHorizontal] at laterPort
    rw [earlierPort] at earlierContact
    rw [laterPort] at laterContact outside
    rw [earlierPort]
    have earlierContactX := congrArg Prod.fst earlierContact
    have earlierContactY := congrArg Prod.snd earlierContact
    have laterContactX := congrArg Prod.fst laterContact
    have laterContactY := congrArg Prod.snd laterContact
    rw [shared] at earlierContactX earlierContactY
    simp only [Cell.add, CornerPort.position] at earlierContactX
    simp only [Cell.add, CornerPort.position] at earlierContactY
    simp only [Cell.add, CornerPort.position] at laterContactX
    simp only [Cell.add, CornerPort.position] at laterContactY
    simp only [CornerPort.OutsideCarrierBoundaryAt,
      CornerPort.InsideCarrierBoundaryAt,
      CornerPort.OutsideCarrierBoundary,
      CornerPort.InsideCarrierBoundary, Cell.sub] at outside ⊢
    omega
  · have earlierSecondNotHorizontal :
      ¬earlier.second.isHorizontal = true := by
        intro secondHorizontal
        exact horizontal (earlierAxis.mpr secondHorizontal)
    have laterFirstNotHorizontal :
      ¬later.first.isHorizontal = true := by
      rw [← shared]
      exact earlierSecondNotHorizontal
    rw [if_neg horizontal] at earlierPort
    rw [if_neg laterFirstNotHorizontal] at laterPort
    rw [earlierPort] at earlierContact
    rw [laterPort] at laterContact outside
    rw [earlierPort]
    have earlierContactX := congrArg Prod.fst earlierContact
    have earlierContactY := congrArg Prod.snd earlierContact
    have laterContactX := congrArg Prod.fst laterContact
    have laterContactY := congrArg Prod.snd laterContact
    rw [shared] at earlierContactX earlierContactY
    simp only [Cell.add, CornerPort.position] at earlierContactX
    simp only [Cell.add, CornerPort.position] at earlierContactY
    simp only [Cell.add, CornerPort.position] at laterContactX
    simp only [Cell.add, CornerPort.position] at laterContactY
    simp only [CornerPort.OutsideCarrierBoundaryAt,
      CornerPort.InsideCarrierBoundaryAt,
      CornerPort.OutsideCarrierBoundary,
      CornerPort.InsideCarrierBoundary, Cell.sub] at outside ⊢
    omega

/-- Strictly ordered nonadjacent raw retained links on one carrier have
separated explicit rectangles. -/
theorem
    retainedDrawingCompleteCarrierLinksRaw_rectanglesSeparated_of_order_of_ne
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {earlier later : EqualityLink CarrierNode}
    (earlierMem :
      earlier ∈ retainedDrawingCompleteCarrierLinksRaw graph)
    (laterMem :
      later ∈ retainedDrawingCompleteCarrierLinksRaw graph)
    (sameKey :
      earlier.first.carrierKey = later.first.carrierKey)
    (ordered :
      earlier.second.orderCoordinate graph ≤
        later.first.orderCoordinate graph)
    (notShared : earlier.second ≠ later.first) :
    ClosedGridRectanglesSeparated
      (drawingCompleteCarrierLinkRectangleLower graph earlier)
      (drawingCompleteCarrierLinkRectangleUpper graph earlier)
      (drawingCompleteCarrierLinkRectangleLower graph later)
      (drawingCompleteCarrierLinkRectangleUpper graph later) := by
  have earlierEndpoints :=
    retainedDrawingCompleteCarrierLinkRaw_endpoints_mem graph earlierMem
  have laterEndpoints :=
    retainedDrawingCompleteCarrierLinkRaw_endpoints_mem graph laterMem
  have earlierCommon :=
    retainedDrawingCompleteCarrierLinksRaw_common_key graph earlierMem
  have endpointKeyEqual :
      earlier.second.carrierKey = later.first.carrierKey :=
    earlierCommon.symm.trans sameKey
  have coordinateDifferent :
      earlier.second.orderCoordinate graph ≠
        later.first.orderCoordinate graph := by
    intro coordinateEqual
    exact notShared
      (retainedCarrierNode_eq_of_commonCarrier_orderCoordinate_eq
        wellFormed degree isLocal
        earlierEndpoints.2 laterEndpoints.1
        endpointKeyEqual coordinateEqual)
  have strict :
      earlier.second.orderCoordinate graph <
        later.first.orderCoordinate graph :=
    lt_of_le_of_ne ordered coordinateDifferent
  have earlierAxis :=
    retainedDrawingCompleteCarrierLinkRaw_first_isHorizontal_iff_second
      wellFormed degree isLocal earlierMem
  have endpointAxis :=
    retainedCarrierNode_isHorizontal_iff_of_commonCarrier
      wellFormed degree isLocal
      earlierEndpoints.2 laterEndpoints.1 endpointKeyEqual
  by_cases horizontal : earlier.first.isHorizontal = true
  · have earlierSecondHorizontal := earlierAxis.mp horizontal
    have laterFirstHorizontal := endpointAxis.mp earlierSecondHorizontal
    simp [drawingCompleteCarrierLinkRectangleLower,
      drawingCompleteCarrierLinkRectangleUpper,
      horizontal, CarrierNode.orderCoordinate,
      earlierSecondHorizontal, laterFirstHorizontal] at strict ⊢
    exact Or.inl strict
  · have earlierSecondNotHorizontal :
      ¬earlier.second.isHorizontal = true := by
        intro secondHorizontal
        exact horizontal (earlierAxis.mpr secondHorizontal)
    have laterFirstNotHorizontal :
        ¬later.first.isHorizontal = true := by
      intro laterHorizontal
      exact earlierSecondNotHorizontal (endpointAxis.mpr laterHorizontal)
    simp [drawingCompleteCarrierLinkRectangleLower,
      drawingCompleteCarrierLinkRectangleUpper,
      horizontal, CarrierNode.orderCoordinate,
      earlierSecondNotHorizontal, laterFirstNotHorizontal] at strict ⊢
    exact Or.inr (Or.inr (Or.inl strict))

/-- Genuine routes of an earlier raw retained link avoid genuine routes of
a later raw retained link on the same carrier. -/
theorem
    retainedDrawingPlanarSATCarrierCarrierRoutesAvoidEachOther_of_raw_order
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {earlier later : EqualityLink CarrierNode}
    (earlierMem :
      earlier ∈ retainedDrawingCompleteCarrierLinksRaw
        formula.incidenceGraph)
    (laterMem :
      later ∈ retainedDrawingCompleteCarrierLinksRaw
        formula.incidenceGraph)
    (sameKey :
      earlier.first.carrierKey = later.first.carrierKey)
    (ordered :
      earlier.second.orderCoordinate formula.incidenceGraph ≤
        later.first.orderCoordinate formula.incidenceGraph)
    {earlierClause :
      EmbeddedClause (PlanarSATVariable Variable)}
    {earlierClauseIndex : Nat}
    (earlierClauseMember :
      (earlierClause, earlierClauseIndex) ∈
        (drawingPlanarSATCarrierLensIncidenceDrawing
          formula earlier).formula.zipIdx)
    {earlierLiteral : PlanarSATVariable Variable × Bool}
    {earlierLiteralIndex : Nat}
    (earlierLiteralMember :
      (earlierLiteral, earlierLiteralIndex) ∈
        earlierClause.literals.zipIdx)
    {laterClause :
      EmbeddedClause (PlanarSATVariable Variable)}
    {laterClauseIndex : Nat}
    (laterClauseMember :
      (laterClause, laterClauseIndex) ∈
        (drawingPlanarSATCarrierLensIncidenceDrawing
          formula later).formula.zipIdx)
    {laterLiteral : PlanarSATVariable Variable × Bool}
    {laterLiteralIndex : Nat}
    (laterLiteralMember :
      (laterLiteral, laterLiteralIndex) ∈
        laterClause.literals.zipIdx) :
    EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
      ((drawingPlanarSATCarrierLensIncidenceDrawing
        formula earlier).routes
          earlierClauseIndex earlierLiteralIndex)
      ((drawingPlanarSATCarrierLensIncidenceDrawing
        formula later).routes
          laterClauseIndex laterLiteralIndex) := by
  let graph := formula.incidenceGraph
  by_cases shared : earlier.second = later.first
  · have laterInside :=
      (retainedDrawingPlanarSATCarrierLensIncidenceDrawing_routePoints_outsideFirst_of_raw
        wellFormed degree isLocal laterMem).mono
        (retainedDrawingCompleteCarrierLinksRaw_firstExterior_insideSecondBoundary_of_shared
          wellFormed degree isLocal earlierMem laterMem shared)
    have earlierContact :=
      EqualityLink.add_secondCarrierMacroOrigin_portPosition
        (retainedDrawingCompleteCarrierLinkRaw_lensGeometry
          wellFormed degree isLocal earlierMem)
    have laterContact :=
      EqualityLink.add_firstCarrierMacroOrigin_portPosition
        (CarrierNode.position graph) later
    have contactEqual :
        Cell.add
            (EqualityLink.secondCarrierMacroOrigin
              (CarrierNode.position graph) earlier)
            (EqualityLink.secondCarrierPort
              (CarrierNode.position graph) earlier).position =
          Cell.add
            (EqualityLink.firstCarrierMacroOrigin
              (CarrierNode.position graph) later)
            (EqualityLink.firstCarrierPort
              (CarrierNode.position graph) later).position := by
      rw [earlierContact, laterContact, shared]
    have laterContacts :=
      retainedDrawingPlanarSATCarrierLensIncidenceDrawing_routeContactsAt_first_of_raw
        wellFormed degree isLocal laterMem
    rw [← contactEqual] at laterContacts
    exact
      drawingRoutesAvoidEachOther_of_members_of_outside_insideCarrierBoundaryAt
        (EqualityLink.secondCarrierPort
          (CarrierNode.position graph) earlier)
        (EqualityLink.secondCarrierMacroOrigin
          (CarrierNode.position graph) earlier)
        (retainedDrawingPlanarSATCarrierLensIncidenceDrawing_routePoints_outsideSecond_of_raw
          wellFormed degree isLocal earlierMem)
        laterInside
        (retainedDrawingPlanarSATCarrierLensIncidenceDrawing_routeContactsAt_second_of_raw
          wellFormed degree isLocal earlierMem)
        laterContacts
        earlierClauseMember earlierLiteralMember
        laterClauseMember laterLiteralMember
  · exact
      retainedDrawingPlanarSATCarrierCarrierRoutesAvoidEachOther_of_raw_rectanglesSeparated
        wellFormed degree isLocal earlierMem laterMem
        (retainedDrawingCompleteCarrierLinksRaw_rectanglesSeparated_of_order_of_ne
          wellFormed degree isLocal earlierMem laterMem
          sameKey ordered shared)
        earlierClauseMember earlierLiteralMember
        laterClauseMember laterLiteralMember

/-- Distinct raw retained links on one carrier have pairwise separated
genuine routes. -/
theorem
    retainedDrawingPlanarSATCarrierCarrierRoutesAvoidEachOther_of_raw_same_key
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {firstLink secondLink : EqualityLink CarrierNode}
    (firstMem :
      firstLink ∈ retainedDrawingCompleteCarrierLinksRaw
        formula.incidenceGraph)
    (secondMem :
      secondLink ∈ retainedDrawingCompleteCarrierLinksRaw
        formula.incidenceGraph)
    (different : firstLink ≠ secondLink)
    (sameKey :
      firstLink.first.carrierKey = secondLink.first.carrierKey)
    {firstClause :
      EmbeddedClause (PlanarSATVariable Variable)}
    {firstClauseIndex : Nat}
    (firstClauseMember :
      (firstClause, firstClauseIndex) ∈
        (drawingPlanarSATCarrierLensIncidenceDrawing
          formula firstLink).formula.zipIdx)
    {firstLiteral : PlanarSATVariable Variable × Bool}
    {firstLiteralIndex : Nat}
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈
        firstClause.literals.zipIdx)
    {secondClause :
      EmbeddedClause (PlanarSATVariable Variable)}
    {secondClauseIndex : Nat}
    (secondClauseMember :
      (secondClause, secondClauseIndex) ∈
        (drawingPlanarSATCarrierLensIncidenceDrawing
          formula secondLink).formula.zipIdx)
    {secondLiteral : PlanarSATVariable Variable × Bool}
    {secondLiteralIndex : Nat}
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈
        secondClause.literals.zipIdx) :
    EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
      ((drawingPlanarSATCarrierLensIncidenceDrawing
        formula firstLink).routes
          firstClauseIndex firstLiteralIndex)
      ((drawingPlanarSATCarrierLensIncidenceDrawing
        formula secondLink).routes
          secondClauseIndex secondLiteralIndex) := by
  rcases
      retainedDrawingCompleteCarrierLinksRaw_same_key_orderCoordinate
        wellFormed degree isLocal firstMem secondMem
        different sameKey with
      firstBeforeSecond | secondBeforeFirst
  · exact
      retainedDrawingPlanarSATCarrierCarrierRoutesAvoidEachOther_of_raw_order
        wellFormed degree isLocal firstMem secondMem
        sameKey firstBeforeSecond
        firstClauseMember firstLiteralMember
        secondClauseMember secondLiteralMember
  · exact EmbeddedCNFIncidenceDrawing.routesAvoidEachOther_comm
      (retainedDrawingPlanarSATCarrierCarrierRoutesAvoidEachOther_of_raw_order
        wellFormed degree isLocal secondMem firstMem
        sameKey.symm secondBeforeFirst
        secondClauseMember secondLiteralMember
        firstClauseMember firstLiteralMember)

end PeriodicOrthocrossing
end LeanTrominoes
