import LeanTrominoes.PeriodicOrthocrossingCarrierAxisInterface
import LeanTrominoes.PeriodicOrthocrossingWireIncidenceDrawings

/-!
# Separation of equality lenses on one carrier

Distinct retained links on one complete carrier have nonoverlapping axial
intervals.  At the boundary where the earlier lens ends, the later lens's
first-end exterior lies on the complementary internal side.  This separates
every genuine route pair, including the adjacent-link case where both links
share one endpoint.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- The first-end exterior of a later link lies inside the second carrier
boundary of an earlier link on the same carrier. -/
theorem
    drawingCompleteCarrierLinks_firstExterior_insideSecondBoundary_of_order
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {earlier later : EqualityLink CarrierNode}
    (earlierMem :
      earlier ∈ drawingCompleteCarrierLinks graph)
    (laterMem :
      later ∈ drawingCompleteCarrierLinks graph)
    (sameKey :
      earlier.first.carrierKey =
        later.first.carrierKey)
    (ordered :
      earlier.second.orderCoordinate graph ≤
        later.first.orderCoordinate graph)
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
  have earlierEndpoints :=
    drawingCompleteCarrierLink_endpoints_mem graph earlierMem
  have laterEndpoints :=
    drawingCompleteCarrierLink_endpoints_mem graph laterMem
  have earlierCommon :=
    drawingCompleteCarrierLinks_common_key graph earlierMem
  have endpointKeyEqual :
      earlier.second.carrierKey =
        later.first.carrierKey :=
    earlierCommon.symm.trans sameKey
  have sameAxis :=
    carrierNode_isHorizontal_iff_of_commonCarrier
      wellFormed degree isLocal
      earlierEndpoints.2 laterEndpoints.1 endpointKeyEqual
  have earlierLinkAxis :=
    drawingCompleteCarrierLink_first_isHorizontal_iff_second
      wellFormed degree isLocal earlierMem
  have axisData :=
    carrierNode_commonCarrier_axis_data
      wellFormed degree isLocal
      earlierEndpoints.2 laterEndpoints.1 endpointKeyEqual
  have earlierPort :=
    drawingCompleteCarrierLink_secondCarrierPort_eq_axis
      wellFormed degree isLocal earlierMem
  have laterPort :=
    drawingCompleteCarrierLink_firstCarrierPort_eq_axis
      wellFormed degree isLocal laterMem
  have earlierContact :=
    EqualityLink.add_secondCarrierMacroOrigin_portPosition
      (drawingCompleteCarrierLink_lensGeometry
        wellFormed degree isLocal earlierMem)
  have laterContact :=
    EqualityLink.add_firstCarrierMacroOrigin_portPosition
      (CarrierNode.position graph) later
  by_cases horizontal : earlier.first.isHorizontal = true
  · have earlierSecondHorizontal :=
      earlierLinkAxis.mp horizontal
    have laterFirstHorizontal :=
      sameAxis.mp earlierSecondHorizontal
    rw [if_pos horizontal] at earlierPort
    rw [if_pos laterFirstHorizontal] at laterPort
    rw [if_pos earlierSecondHorizontal] at axisData
    simp [CarrierNode.orderCoordinate,
      earlierSecondHorizontal, laterFirstHorizontal] at ordered
    rw [earlierPort] at earlierContact
    rw [laterPort] at laterContact outside
    rw [earlierPort]
    have earlierContactX :=
      congrArg Prod.fst earlierContact
    have earlierContactY :=
      congrArg Prod.snd earlierContact
    have laterContactX :=
      congrArg Prod.fst laterContact
    have laterContactY :=
      congrArg Prod.snd laterContact
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
        intro earlierSecondHorizontal
        exact horizontal (earlierLinkAxis.mpr earlierSecondHorizontal)
    have laterFirstNotHorizontal :
      ¬later.first.isHorizontal = true := by
        intro laterFirstHorizontal
        exact earlierSecondNotHorizontal
          (sameAxis.mpr laterFirstHorizontal)
    rw [if_neg horizontal] at earlierPort
    rw [if_neg laterFirstNotHorizontal] at laterPort
    rw [if_neg earlierSecondNotHorizontal] at axisData
    simp [CarrierNode.orderCoordinate,
      earlierSecondNotHorizontal,
      laterFirstNotHorizontal] at ordered
    rw [earlierPort] at earlierContact
    rw [laterPort] at laterContact outside
    rw [earlierPort]
    have earlierContactX :=
      congrArg Prod.fst earlierContact
    have earlierContactY :=
      congrArg Prod.snd earlierContact
    have laterContactX :=
      congrArg Prod.fst laterContact
    have laterContactY :=
      congrArg Prod.snd laterContact
    simp only [Cell.add, CornerPort.position] at earlierContactX
    simp only [Cell.add, CornerPort.position] at earlierContactY
    simp only [Cell.add, CornerPort.position] at laterContactX
    simp only [Cell.add, CornerPort.position] at laterContactY
    simp only [CornerPort.OutsideCarrierBoundaryAt,
      CornerPort.InsideCarrierBoundaryAt,
      CornerPort.OutsideCarrierBoundary,
      CornerPort.InsideCarrierBoundary, Cell.sub] at outside ⊢
    omega

/-- The later lens can meet the earlier link's second carrier port only at
an advertised endpoint of its route. -/
theorem
    drawingPlanarSATCarrierLensIncidenceDrawing_routeContactsAt_earlierSecond
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    {earlier later : EqualityLink CarrierNode}
    (earlierMem :
      earlier ∈ drawingCompleteCarrierLinks
        (PeriodicCNF.incidenceGraph formula))
    (laterMem :
      later ∈ drawingCompleteCarrierLinks
        (PeriodicCNF.incidenceGraph formula))
    (sameKey :
      earlier.first.carrierKey =
        later.first.carrierKey)
    (ordered :
      earlier.second.orderCoordinate
          (PeriodicCNF.incidenceGraph formula) ≤
        later.first.orderCoordinate
          (PeriodicCNF.incidenceGraph formula)) :
    (drawingPlanarSATCarrierLensIncidenceDrawing
      formula later).RouteContactsAtEndpoint
        (Cell.add
          (EqualityLink.secondCarrierMacroOrigin
            (CarrierNode.position
              (PeriodicCNF.incidenceGraph formula))
            earlier)
          (EqualityLink.secondCarrierPort
            (CarrierNode.position
              (PeriodicCNF.incidenceGraph formula))
            earlier).position) := by
  let graph := PeriodicCNF.incidenceGraph formula
  have earlierEndpoints :=
    drawingCompleteCarrierLink_endpoints_mem graph earlierMem
  have laterEndpoints :=
    drawingCompleteCarrierLink_endpoints_mem graph laterMem
  have earlierCommon :=
    drawingCompleteCarrierLinks_common_key graph earlierMem
  have endpointKeyEqual :
      earlier.second.carrierKey =
        later.first.carrierKey :=
    earlierCommon.symm.trans sameKey
  have sameAxis :=
    carrierNode_isHorizontal_iff_of_commonCarrier
      wellFormed degree isLocal
      earlierEndpoints.2 laterEndpoints.1 endpointKeyEqual
  have earlierLinkAxis :=
    drawingCompleteCarrierLink_first_isHorizontal_iff_second
      wellFormed degree isLocal earlierMem
  have earlierContact :=
    EqualityLink.add_secondCarrierMacroOrigin_portPosition
      (drawingCompleteCarrierLink_lensGeometry
        wellFormed degree isLocal earlierMem)
  have laterContact :=
    EqualityLink.add_firstCarrierMacroOrigin_portPosition
      (CarrierNode.position graph) later
  have laterBounded :=
    drawingPlanarSATCarrierLensIncidenceDrawing_routePoints_outsideFirst
      wellFormed degree isLocal laterMem
  have laterContacts :=
    drawingPlanarSATCarrierLensIncidenceDrawing_routeContactsAt_first
      wellFormed degree isLocal laterMem
  intro incidenceIndex point pointMember pointEqual
  by_cases endpointEqual : earlier.second = later.first
  · have contactEqual :
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
      rw [earlierContact, laterContact, endpointEqual]
    exact laterContacts incidenceIndex point pointMember
      (pointEqual.trans contactEqual)
  · have coordinateDifferent :
      earlier.second.orderCoordinate graph ≠
        later.first.orderCoordinate graph := by
      intro coordinateEqual
      exact endpointEqual
        (carrierNode_eq_of_commonCarrier_orderCoordinate_eq
          wellFormed degree isLocal
          earlierEndpoints.2 laterEndpoints.1
          endpointKeyEqual coordinateEqual)
    have strict :
      earlier.second.orderCoordinate graph <
        later.first.orderCoordinate graph :=
      lt_of_le_of_ne ordered coordinateDifferent
    have earlierPort :=
      drawingCompleteCarrierLink_secondCarrierPort_eq_axis
        wellFormed degree isLocal earlierMem
    have laterPort :=
      drawingCompleteCarrierLink_firstCarrierPort_eq_axis
        wellFormed degree isLocal laterMem
    have axisData :=
      carrierNode_commonCarrier_axis_data
        wellFormed degree isLocal
        earlierEndpoints.2 laterEndpoints.1 endpointKeyEqual
    have pointOutside :=
      laterBounded incidenceIndex point pointMember
    rw [pointEqual] at pointOutside
    by_cases horizontal : earlier.first.isHorizontal = true
    · have earlierSecondHorizontal :=
        earlierLinkAxis.mp horizontal
      have laterFirstHorizontal :=
        sameAxis.mp earlierSecondHorizontal
      rw [if_pos horizontal] at earlierPort
      rw [if_pos laterFirstHorizontal] at laterPort
      rw [if_pos earlierSecondHorizontal] at axisData
      simp [CarrierNode.orderCoordinate,
        earlierSecondHorizontal, laterFirstHorizontal] at strict
      rw [earlierPort] at earlierContact pointOutside
      rw [laterPort] at laterContact pointOutside
      have earlierContactX :=
        congrArg Prod.fst earlierContact
      have earlierContactY :=
        congrArg Prod.snd earlierContact
      have laterContactX :=
        congrArg Prod.fst laterContact
      have laterContactY :=
        congrArg Prod.snd laterContact
      simp only [Cell.add, CornerPort.position] at earlierContactX
      simp only [Cell.add, CornerPort.position] at earlierContactY
      simp only [Cell.add, CornerPort.position] at laterContactX
      simp only [Cell.add, CornerPort.position] at laterContactY
      simp only [CornerPort.OutsideCarrierBoundaryAt,
        CornerPort.OutsideCarrierBoundary, Cell.sub,
        Cell.add, CornerPort.position] at pointOutside
      have strictX :
          (earlier.second.position
              (PeriodicCNF.incidenceGraph formula)).1 <
            (later.first.position
              (PeriodicCNF.incidenceGraph formula)).1 := by
        simpa [graph] using strict
      have sameY :
          (earlier.second.position
              (PeriodicCNF.incidenceGraph formula)).2 =
            (later.first.position
              (PeriodicCNF.incidenceGraph formula)).2 := by
        simpa [graph] using axisData.1
      have earlierContactX' :
          (EqualityLink.secondCarrierMacroOrigin
              (CarrierNode.position
                (PeriodicCNF.incidenceGraph formula))
              earlier).1 + 1 =
            (earlier.second.position
              (PeriodicCNF.incidenceGraph formula)).1 := by
        simpa [graph] using earlierContactX
      have laterContactX' :
          (EqualityLink.firstCarrierMacroOrigin
              (CarrierNode.position
                (PeriodicCNF.incidenceGraph formula))
              later).1 + 11 =
            (later.first.position
              (PeriodicCNF.incidenceGraph formula)).1 := by
        simpa [graph] using laterContactX
      omega
    · have earlierSecondNotHorizontal :
        ¬earlier.second.isHorizontal = true := by
          intro earlierSecondHorizontal
          exact horizontal (earlierLinkAxis.mpr earlierSecondHorizontal)
      have laterFirstNotHorizontal :
        ¬later.first.isHorizontal = true := by
          intro laterFirstHorizontal
          exact earlierSecondNotHorizontal
            (sameAxis.mpr laterFirstHorizontal)
      rw [if_neg horizontal] at earlierPort
      rw [if_neg laterFirstNotHorizontal] at laterPort
      rw [if_neg earlierSecondNotHorizontal] at axisData
      simp [CarrierNode.orderCoordinate,
        earlierSecondNotHorizontal,
        laterFirstNotHorizontal] at strict
      rw [earlierPort] at earlierContact pointOutside
      rw [laterPort] at laterContact pointOutside
      have earlierContactX :=
        congrArg Prod.fst earlierContact
      have earlierContactY :=
        congrArg Prod.snd earlierContact
      have laterContactX :=
        congrArg Prod.fst laterContact
      have laterContactY :=
        congrArg Prod.snd laterContact
      simp only [Cell.add, CornerPort.position] at earlierContactX
      simp only [Cell.add, CornerPort.position] at earlierContactY
      simp only [Cell.add, CornerPort.position] at laterContactX
      simp only [Cell.add, CornerPort.position] at laterContactY
      simp only [CornerPort.OutsideCarrierBoundaryAt,
        CornerPort.OutsideCarrierBoundary, Cell.sub,
        Cell.add, CornerPort.position] at pointOutside
      have strictY :
          (earlier.second.position
              (PeriodicCNF.incidenceGraph formula)).2 <
            (later.first.position
              (PeriodicCNF.incidenceGraph formula)).2 := by
        simpa [graph] using strict
      have sameX :
          (earlier.second.position
              (PeriodicCNF.incidenceGraph formula)).1 =
            (later.first.position
              (PeriodicCNF.incidenceGraph formula)).1 := by
        simpa [graph] using axisData.1
      have earlierContactY' :
          (EqualityLink.secondCarrierMacroOrigin
              (CarrierNode.position
                (PeriodicCNF.incidenceGraph formula))
              earlier).2 + 1 =
            (earlier.second.position
              (PeriodicCNF.incidenceGraph formula)).2 := by
        simpa [graph] using earlierContactY
      have laterContactY' :
          (EqualityLink.firstCarrierMacroOrigin
              (CarrierNode.position
                (PeriodicCNF.incidenceGraph formula))
              later).2 + 11 =
            (later.first.position
              (PeriodicCNF.incidenceGraph formula)).2 := by
        simpa [graph] using laterContactY
      omega

/-- Every genuine route of an earlier carrier lens avoids every genuine
route of a later lens on the same carrier. -/
theorem drawingPlanarSATCarrierCarrierRoutesAvoidEachOther_of_order
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    {earlier later : EqualityLink CarrierNode}
    (earlierMem :
      earlier ∈ drawingCompleteCarrierLinks
        (PeriodicCNF.incidenceGraph formula))
    (laterMem :
      later ∈ drawingCompleteCarrierLinks
        (PeriodicCNF.incidenceGraph formula))
    (sameKey :
      earlier.first.carrierKey =
        later.first.carrierKey)
    (ordered :
      earlier.second.orderCoordinate
          (PeriodicCNF.incidenceGraph formula) ≤
        later.first.orderCoordinate
          (PeriodicCNF.incidenceGraph formula))
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
  let graph := PeriodicCNF.incidenceGraph formula
  have laterInside :=
    (drawingPlanarSATCarrierLensIncidenceDrawing_routePoints_outsideFirst
      wellFormed degree isLocal laterMem).mono
        (drawingCompleteCarrierLinks_firstExterior_insideSecondBoundary_of_order
          wellFormed degree isLocal earlierMem laterMem
          sameKey ordered)
  exact
    drawingRoutesAvoidEachOther_of_members_of_outside_insideCarrierBoundaryAt
      (EqualityLink.secondCarrierPort
        (CarrierNode.position graph) earlier)
      (EqualityLink.secondCarrierMacroOrigin
        (CarrierNode.position graph) earlier)
      (drawingPlanarSATCarrierLensIncidenceDrawing_routePoints_outsideSecond
        wellFormed degree isLocal earlierMem)
      laterInside
      (drawingPlanarSATCarrierLensIncidenceDrawing_routeContactsAt_second
        wellFormed degree isLocal earlierMem)
      (drawingPlanarSATCarrierLensIncidenceDrawing_routeContactsAt_earlierSecond
        wellFormed degree isLocal earlierMem laterMem sameKey ordered)
      earlierClauseMember earlierLiteralMember
      laterClauseMember laterLiteralMember

/-- Distinct retained links on one complete carrier have pairwise separated
genuine routes. -/
theorem drawingPlanarSATCarrierCarrierRoutesAvoidEachOther_of_same_key
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    {firstLink secondLink : EqualityLink CarrierNode}
    (firstMem :
      firstLink ∈ drawingCompleteCarrierLinks
        (PeriodicCNF.incidenceGraph formula))
    (secondMem :
      secondLink ∈ drawingCompleteCarrierLinks
        (PeriodicCNF.incidenceGraph formula))
    (different : firstLink ≠ secondLink)
    (sameKey :
      firstLink.first.carrierKey =
        secondLink.first.carrierKey)
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
      drawingCompleteCarrierLinks_same_key_orderCoordinate
        wellFormed degree isLocal firstMem secondMem
        different sameKey with
      firstBeforeSecond | secondBeforeFirst
  · exact
      drawingPlanarSATCarrierCarrierRoutesAvoidEachOther_of_order
        wellFormed degree isLocal firstMem secondMem
        sameKey firstBeforeSecond
        firstClauseMember firstLiteralMember
        secondClauseMember secondLiteralMember
  · exact EmbeddedCNFIncidenceDrawing.routesAvoidEachOther_comm
      (drawingPlanarSATCarrierCarrierRoutesAvoidEachOther_of_order
        wellFormed degree isLocal secondMem firstMem
        sameKey.symm secondBeforeFirst
        secondClauseMember secondLiteralMember
        firstClauseMember firstLiteralMember)

end PeriodicOrthocrossing
end LeanTrominoes
