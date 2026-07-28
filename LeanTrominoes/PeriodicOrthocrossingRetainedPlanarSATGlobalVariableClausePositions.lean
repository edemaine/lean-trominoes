import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATNoncarrierVariableClausePositions
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATCarrierClausePositions
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATCarrierNoncarrierClausePositions

/-!
# Global separation of retained variable and clause positions

This file proves the remaining cross-part vertex obligation for the retained
planar-SAT drawing: no used variable position is a clause position.

For a carrier lens, every used variable is first lifted back to one local
component that contains it.  A non-carrier component is either rectangle
separated from the lens or meets it at a certified carrier boundary, whose
only common point is a lens endpoint.  Two carrier lenses are rectangle
separated except when consecutive links share an endpoint; forward clearance
settles that exceptional case.  The non-carrier clause case is supplied by
the fixed-coordinate classification in the preceding module.
-/

namespace LeanTrominoes

open PlanarThreeSAT

namespace PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- A used variable position inherits every pointwise predicate satisfied by
all routes of an incidence drawing. -/
theorem variablePosition_satisfies
    {Variable : Type*} [DecidableEq Variable]
    (drawing : EmbeddedCNFIncidenceDrawing Variable)
    (routesMatch : drawing.RoutesMatch)
    {predicate : Cell → Prop}
    (bounded : drawing.RoutePointsSatisfy predicate)
    {atom : Variable}
    (atomMember : atom ∈ drawing.variableVertices) :
    predicate (drawing.variablePosition atom) := by
  rw [variableVertices, List.mem_dedup] at atomMember
  rcases List.mem_flatMap.mp atomMember with
    ⟨clause, clauseMember, literalMember⟩
  rcases List.mem_map.mp literalMember with
    ⟨literal, literalMember, atomEq⟩
  rcases List.mem_iff_get.mp clauseMember with
    ⟨clauseIndex, clauseEq⟩
  rcases List.mem_iff_get.mp literalMember with
    ⟨literalIndex, literalEq⟩
  have taggedClauseMember :
      (clause, clauseIndex.1) ∈ drawing.formula.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?,
      List.getElem?_eq_some_iff]
    exact ⟨clauseIndex.2, by simpa using clauseEq⟩
  have taggedLiteralMember :
      (literal, literalIndex.1) ∈ clause.literals.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?,
      List.getElem?_eq_some_iff]
    exact ⟨literalIndex.2, by simpa using literalEq⟩
  have endpoints :=
    drawing.physicalRoutesMatch routesMatch
      clause clauseIndex.1 taggedClauseMember
      literal literalIndex.1 taggedLiteralMember
  have positionMember :
      drawing.variablePosition atom ∈
        drawing.routes clauseIndex.1 literalIndex.1 := by
    apply mem_of_getLast?_eq_some
    simpa [atomEq] using endpoints.2
  exact bounded.of_members
    taggedClauseMember taggedLiteralMember positionMember

end PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

namespace PeriodicOrthocrossing

set_option maxHeartbeats 1200000

/-- Every globally used retained variable occurs in at least one
metadata-selected local component drawing. -/
theorem retainedVariable_has_localMetadata
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (atom : PlanarSATVariable Variable)
    (member :
      atom ∈
        (retainedDrawingPlanarSATLocalIncidenceDrawing
          formula).variableVertices) :
    ∃ metadata ∈ retainedDrawingPlanarSATClauseMetadata formula,
      metadata.RetainedValid formula ∧
        atom ∈
          (metadata.source.incidenceDrawing
            formula).variableVertices := by
  rw [EmbeddedCNFIncidenceDrawing.variableVertices,
    retainedDrawingPlanarSATLocalIncidenceDrawing_formula,
    List.mem_dedup] at member
  rcases List.mem_flatMap.mp member with
    ⟨clause, clauseMember, atomMember⟩
  rcases List.mem_map.mp atomMember with
    ⟨literal, literalMember, atomEqual⟩
  rw [← retainedDrawingPlanarSATClauseMetadata_clauses]
    at clauseMember
  rcases List.mem_map.mp clauseMember with
    ⟨metadata, metadataMember, metadataClauseEqual⟩
  subst clause
  have valid :=
    retainedDrawingPlanarSATClauseMetadata_valid
      formula metadataMember
  have localClauseMember :=
    metadata.retainedLocalClauseMember
      wellFormed degree isLocal valid
  refine ⟨metadata, metadataMember, valid, ?_⟩
  rw [EmbeddedCNFIncidenceDrawing.variableVertices,
    List.mem_dedup]
  apply List.mem_flatMap.mpr
  refine
    ⟨metadata.clause,
      List.fst_mem_of_mem_zipIdx localClauseMember, ?_⟩
  exact List.mem_map.mpr
    ⟨literal, literalMember, atomEqual⟩

/-- Complementary carrier-boundary bounds force any common carrier-clause
and local-variable point to a lens endpoint, which local planarity excludes. -/
theorem retainedCarrierClausePosition_ne_variable_of_boundary
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem :
      link ∈ retainedDrawingCompleteCarrierLinks
        (PeriodicCNF.incidenceGraph formula))
    {carrierClause :
      EmbeddedClause (PlanarSATVariable Variable)}
    {carrierClauseIndex : Nat}
    (carrierClauseMember :
      (carrierClause, carrierClauseIndex) ∈
        (drawingPlanarSATCarrierLensIncidenceDrawing
          formula link).formula.zipIdx)
    {otherDrawing :
      EmbeddedCNFIncidenceDrawing (PlanarSATVariable Variable)}
    {atom : PlanarSATVariable Variable}
    (atomMember : atom ∈ otherDrawing.variableVertices)
    (otherRoutesMatch : otherDrawing.RoutesMatch)
    (port : CornerPort)
    (origin : Cell)
    (carrierOutside :
      (drawingPlanarSATCarrierLensIncidenceDrawing
        formula link).RoutePointsSatisfy
          (port.OutsideCarrierBoundaryAt origin))
    (otherInside :
      otherDrawing.RoutePointsSatisfy
        (port.InsideCarrierBoundaryAt origin))
    (endpoint :
      Cell.add origin port.position =
          link.first.position
            (PeriodicCNF.incidenceGraph formula) ∨
        Cell.add origin port.position =
          link.second.position
            (PeriodicCNF.incidenceGraph formula)) :
    carrierClause.position ≠
      otherDrawing.variablePosition atom := by
  have carrierOutsideAt :=
    EmbeddedCNFIncidenceDrawing.clausePosition_satisfies
      (drawingPlanarSATCarrierLensIncidenceDrawing formula link)
      (retainedDrawingPlanarSATCarrierLensIncidenceDrawing_isValid
        wellFormed degree isLocal linkMem).1
      carrierOutside carrierClauseMember
      (retainedCarrierClause_literals_ne_nil
        wellFormed degree isLocal linkMem carrierClauseMember)
  have otherInsideAt :=
    EmbeddedCNFIncidenceDrawing.variablePosition_satisfies
      otherDrawing otherRoutesMatch otherInside atomMember
  intro positionEq
  have carrierInsideAt :
      port.InsideCarrierBoundaryAt
        origin carrierClause.position := by
    rw [positionEq]
    exact otherInsideAt
  have portEq :=
    port.eq_add_position_of_insideAt_of_outsideAt
      origin carrierInsideAt carrierOutsideAt
  rcases endpoint with firstEndpoint | secondEndpoint
  · exact
      (retainedCarrierClausePosition_ne_firstNodePosition
        wellFormed degree isLocal linkMem carrierClauseMember)
        (portEq.trans firstEndpoint)
  · exact
      (retainedCarrierClausePosition_ne_secondNodePosition
        wellFormed degree isLocal linkMem carrierClauseMember)
        (portEq.trans secondEndpoint)

/-- A retained carrier clause avoids every variable of an incident
crossover component. -/
theorem retainedCarrierClausePosition_ne_crossoverVariable_of_incident
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem :
      link ∈ retainedDrawingCompleteCarrierLinks
        (PeriodicCNF.incidenceGraph formula))
    {crossing : CrossingRecord}
    (incident : CarrierLinkIncidentToCrossover link crossing)
    {carrierClause :
      EmbeddedClause (PlanarSATVariable Variable)}
    {carrierClauseIndex : Nat}
    (carrierClauseMember :
      (carrierClause, carrierClauseIndex) ∈
        (drawingPlanarSATCarrierLensIncidenceDrawing
          formula link).formula.zipIdx)
    {atom : PlanarSATVariable Variable}
    (atomMember :
      atom ∈
        (drawingPlanarSATCrossoverIncidenceDrawing
          formula crossing).variableVertices) :
    carrierClause.position ≠
      drawingPlanarSATVariablePosition formula atom := by
  rcases incident with ⟨side, firstEqual | secondEqual⟩
  · have portEqual :=
      retainedDrawingCompleteCarrierLink_firstCarrierPort_eq_boundary
        wellFormed degree isLocal linkMem firstEqual
    have originEqual :=
      retainedDrawingCompleteCarrierLink_firstCarrierMacroOrigin_eq_boundary
        wellFormed degree isLocal linkMem firstEqual
    have carrierOutside :=
      retainedDrawingPlanarSATCarrierLensIncidenceDrawing_routePoints_outsideFirst
        wellFormed degree isLocal linkMem
    have endpoint :=
      EqualityLink.add_firstCarrierMacroOrigin_portPosition
        (CarrierNode.position
          (PeriodicCNF.incidenceGraph formula)) link
    rw [portEqual, originEqual] at carrierOutside endpoint
    exact
      retainedCarrierClausePosition_ne_variable_of_boundary
        wellFormed degree isLocal linkMem carrierClauseMember
        atomMember
        (drawingPlanarSATCrossoverIncidenceDrawing_routesMatch
          formula crossing)
        side.carrierPort (crossingMacroOrigin crossing)
        carrierOutside
        (drawingPlanarSATCrossoverIncidenceDrawing_routePoints_insideCarrierBoundary
          formula crossing side)
        (Or.inl endpoint)
  · have portEqual :=
      retainedDrawingCompleteCarrierLink_secondCarrierPort_eq_boundary
        wellFormed degree isLocal linkMem secondEqual
    have originEqual :=
      retainedDrawingCompleteCarrierLink_secondCarrierMacroOrigin_eq_boundary
        wellFormed degree isLocal linkMem secondEqual
    have carrierOutside :=
      retainedDrawingPlanarSATCarrierLensIncidenceDrawing_routePoints_outsideSecond
        wellFormed degree isLocal linkMem
    have endpoint :=
      EqualityLink.add_secondCarrierMacroOrigin_portPosition
        (retainedDrawingCompleteCarrierLink_lensGeometry
          wellFormed degree isLocal linkMem)
    rw [portEqual, originEqual] at carrierOutside endpoint
    exact
      retainedCarrierClausePosition_ne_variable_of_boundary
        wellFormed degree isLocal linkMem carrierClauseMember
        atomMember
        (drawingPlanarSATCrossoverIncidenceDrawing_routesMatch
          formula crossing)
        side.carrierPort (crossingMacroOrigin crossing)
        carrierOutside
        (drawingPlanarSATCrossoverIncidenceDrawing_routePoints_insideCarrierBoundary
          formula crossing side)
        (Or.inr endpoint)

/-- A retained carrier clause avoids every variable of an incident bend
component. -/
theorem retainedCarrierClausePosition_ne_bendVariable_of_incident
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem :
      link ∈ retainedDrawingCompleteCarrierLinks
        (PeriodicCNF.incidenceGraph formula))
    {routeBend : RouteBend}
    (routeBendMember :
      routeBend ∈
        (drawingRouteBends
          (PeriodicCNF.incidenceGraph formula)).dedup)
    (incident : CarrierLinkIncidentToRouteBend link routeBend)
    {carrierClause :
      EmbeddedClause (PlanarSATVariable Variable)}
    {carrierClauseIndex : Nat}
    (carrierClauseMember :
      (carrierClause, carrierClauseIndex) ∈
        (drawingPlanarSATCarrierLensIncidenceDrawing
          formula link).formula.zipIdx)
    {atom : PlanarSATVariable Variable}
    (atomMember :
      atom ∈
        (drawingPlanarSATBendCornerIncidenceDrawing
          formula routeBend).variableVertices) :
    carrierClause.position ≠
      drawingPlanarSATVariablePosition formula atom := by
  let graph := PeriodicCNF.incidenceGraph formula
  have geometry :
      routeBend.CornerGeometry :=
    drawingRouteBendDedup_cornerGeometry
      wellFormed degree isLocal routeBendMember
  have otherRoutesMatch :=
    (drawingPlanarSATBendCornerIncidenceDrawing_isValid
      wellFormed degree isLocal routeBendMember).1
  rcases incident with
      firstIncoming |
      firstOutgoing |
      secondIncoming |
      secondOutgoing
  · have interface :=
      retainedDrawingCompleteCarrierLink_first_incomingInterface
        wellFormed degree isLocal linkMem
        routeBend geometry firstIncoming
    have carrierOutside :=
      retainedDrawingPlanarSATCarrierLensIncidenceDrawing_routePoints_outsideFirst
        wellFormed degree isLocal linkMem
    have endpoint :=
      EqualityLink.add_firstCarrierMacroOrigin_portPosition
        (CarrierNode.position graph) link
    rw [interface.1, interface.2] at carrierOutside endpoint
    exact
      retainedCarrierClausePosition_ne_variable_of_boundary
        wellFormed degree isLocal linkMem carrierClauseMember
        atomMember otherRoutesMatch
        routeBend.incomingPort
        (Cell.scale planarMacroScale (routeBend.drawingPoint graph))
        carrierOutside
        (drawingPlanarSATBendCornerIncidenceDrawing_routePoints_insideIncoming
          formula routeBend)
        (Or.inl endpoint)
  · have interface :=
      retainedDrawingCompleteCarrierLink_first_outgoingInterface
        wellFormed degree isLocal linkMem
        routeBend geometry firstOutgoing
    have carrierOutside :=
      retainedDrawingPlanarSATCarrierLensIncidenceDrawing_routePoints_outsideFirst
        wellFormed degree isLocal linkMem
    have endpoint :=
      EqualityLink.add_firstCarrierMacroOrigin_portPosition
        (CarrierNode.position graph) link
    rw [interface.1, interface.2] at carrierOutside endpoint
    exact
      retainedCarrierClausePosition_ne_variable_of_boundary
        wellFormed degree isLocal linkMem carrierClauseMember
        atomMember otherRoutesMatch
        routeBend.outgoingPort
        (Cell.scale planarMacroScale (routeBend.drawingPoint graph))
        carrierOutside
        (drawingPlanarSATBendCornerIncidenceDrawing_routePoints_insideOutgoing
          formula routeBend)
        (Or.inl endpoint)
  · have interface :=
      retainedDrawingCompleteCarrierLink_second_incomingInterface
        wellFormed degree isLocal linkMem
        routeBend geometry secondIncoming
    have carrierOutside :=
      retainedDrawingPlanarSATCarrierLensIncidenceDrawing_routePoints_outsideSecond
        wellFormed degree isLocal linkMem
    have endpoint :=
      EqualityLink.add_secondCarrierMacroOrigin_portPosition
        (retainedDrawingCompleteCarrierLink_lensGeometry
          wellFormed degree isLocal linkMem)
    rw [interface.1, interface.2] at carrierOutside endpoint
    exact
      retainedCarrierClausePosition_ne_variable_of_boundary
        wellFormed degree isLocal linkMem carrierClauseMember
        atomMember otherRoutesMatch
        routeBend.incomingPort
        (Cell.scale planarMacroScale (routeBend.drawingPoint graph))
        carrierOutside
        (drawingPlanarSATBendCornerIncidenceDrawing_routePoints_insideIncoming
          formula routeBend)
        (Or.inr endpoint)
  · have interface :=
      retainedDrawingCompleteCarrierLink_second_outgoingInterface
        wellFormed degree isLocal linkMem
        routeBend geometry secondOutgoing
    have carrierOutside :=
      retainedDrawingPlanarSATCarrierLensIncidenceDrawing_routePoints_outsideSecond
        wellFormed degree isLocal linkMem
    have endpoint :=
      EqualityLink.add_secondCarrierMacroOrigin_portPosition
        (retainedDrawingCompleteCarrierLink_lensGeometry
          wellFormed degree isLocal linkMem)
    rw [interface.1, interface.2] at carrierOutside endpoint
    exact
      retainedCarrierClausePosition_ne_variable_of_boundary
        wellFormed degree isLocal linkMem carrierClauseMember
        atomMember otherRoutesMatch
        routeBend.outgoingPort
        (Cell.scale planarMacroScale (routeBend.drawingPoint graph))
        carrierOutside
        (drawingPlanarSATBendCornerIncidenceDrawing_routePoints_insideOutgoing
          formula routeBend)
        (Or.inr endpoint)

/-- A retained carrier clause avoids every variable of an incident routed
variable component. -/
theorem retainedCarrierClausePosition_ne_routedVariable_of_incident
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem :
      link ∈ retainedDrawingCompleteCarrierLinks
        (PeriodicCNF.incidenceGraph formula))
    {site : VariableRouteSite Variable}
    {occurrence : CNFRouteOccurrence Variable}
    (occurrenceMember :
      occurrence ∈ variableRouteOccurrencesAt formula site)
    (drawingArm : DuplicatorArm)
    (routedLink : EqualityLink (PlanarSATNode Variable))
    (incident :
      CarrierLinkIncidentToTargetTerminal formula link occurrence)
    {carrierClause :
      EmbeddedClause (PlanarSATVariable Variable)}
    {carrierClauseIndex : Nat}
    (carrierClauseMember :
      (carrierClause, carrierClauseIndex) ∈
        (drawingPlanarSATCarrierLensIncidenceDrawing
          formula link).formula.zipIdx)
    (otherRoutesMatch :
      (drawingPlanarSATRoutedVariableIncidenceDrawing
        formula site drawingArm routedLink).RoutesMatch)
    {atom : PlanarSATVariable Variable}
    (atomMember :
      atom ∈
        (drawingPlanarSATRoutedVariableIncidenceDrawing
          formula site drawingArm routedLink).variableVertices) :
    carrierClause.position ≠
      drawingPlanarSATVariablePosition formula atom := by
  rcases incident with firstEqual | secondEqual
  · have interface :=
      retainedDrawingCompleteCarrierLink_first_targetTerminalInterface
        wellFormed degree isLocal linkMem
        site occurrenceMember firstEqual
    have carrierOutside :=
      retainedDrawingPlanarSATCarrierLensIncidenceDrawing_routePoints_outsideFirst
        wellFormed degree isLocal linkMem
    have endpoint :=
      EqualityLink.add_firstCarrierMacroOrigin_portPosition
        (CarrierNode.position
          (PeriodicCNF.incidenceGraph formula)) link
    rw [interface.1, interface.2] at carrierOutside endpoint
    exact
      retainedCarrierClausePosition_ne_variable_of_boundary
        wellFormed degree isLocal linkMem carrierClauseMember
        atomMember otherRoutesMatch
        (occurrence.targetTerminal formula).duplicatorArm.carrierPort
        (routedVariableOrigin formula site)
        carrierOutside
        (drawingPlanarSATRoutedVariableIncidenceDrawing_routePoints_insideCarrierBoundaryAtArm
          formula site drawingArm
          (occurrence.targetTerminal formula).duplicatorArm
          routedLink)
        (Or.inl endpoint)
  · have interface :=
      retainedDrawingCompleteCarrierLink_second_targetTerminalInterface
        wellFormed degree isLocal linkMem
        site occurrenceMember secondEqual
    have carrierOutside :=
      retainedDrawingPlanarSATCarrierLensIncidenceDrawing_routePoints_outsideSecond
        wellFormed degree isLocal linkMem
    have endpoint :=
      EqualityLink.add_secondCarrierMacroOrigin_portPosition
        (retainedDrawingCompleteCarrierLink_lensGeometry
          wellFormed degree isLocal linkMem)
    rw [interface.1, interface.2] at carrierOutside endpoint
    exact
      retainedCarrierClausePosition_ne_variable_of_boundary
        wellFormed degree isLocal linkMem carrierClauseMember
        atomMember otherRoutesMatch
        (occurrence.targetTerminal formula).duplicatorArm.carrierPort
        (routedVariableOrigin formula site)
        carrierOutside
        (drawingPlanarSATRoutedVariableIncidenceDrawing_routePoints_insideCarrierBoundaryAtArm
          formula site drawingArm
          (occurrence.targetTerminal formula).duplicatorArm
          routedLink)
        (Or.inr endpoint)

/-- A retained carrier clause avoids every variable of an incident routed
source-clause component. -/
theorem retainedCarrierClausePosition_ne_routedClauseVariable_of_incident
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem :
      link ∈ retainedDrawingCompleteCarrierLinks
        (PeriodicCNF.incidenceGraph formula))
    {site : ClauseRouteSite}
    {occurrence : CNFRouteOccurrence Variable}
    (occurrenceMember :
      occurrence ∈ clauseRouteOccurrencesAt formula site)
    (incident :
      CarrierLinkIncidentToSourceTerminal formula link occurrence)
    {carrierClause :
      EmbeddedClause (PlanarSATVariable Variable)}
    {carrierClauseIndex : Nat}
    (carrierClauseMember :
      (carrierClause, carrierClauseIndex) ∈
        (drawingPlanarSATCarrierLensIncidenceDrawing
          formula link).formula.zipIdx)
    {atom : PlanarSATVariable Variable}
    (atomMember :
      atom ∈
        (drawingPlanarSATRoutedClauseIncidenceDrawing
          formula site).variableVertices) :
    carrierClause.position ≠
      drawingPlanarSATVariablePosition formula atom := by
  have otherRoutesMatch :=
    drawingPlanarSATRoutedClauseIncidenceDrawing_routesMatch
      formula wellFormed site
  rcases incident with firstEqual | secondEqual
  · have interface :=
      retainedDrawingCompleteCarrierLink_first_sourceTerminalInterface
        wellFormed degree isLocal linkMem
        site occurrenceMember firstEqual
    have carrierOutside :=
      retainedDrawingPlanarSATCarrierLensIncidenceDrawing_routePoints_outsideFirst
        wellFormed degree isLocal linkMem
    have endpoint :=
      EqualityLink.add_firstCarrierMacroOrigin_portPosition
        (CarrierNode.position
          (PeriodicCNF.incidenceGraph formula)) link
    rw [interface.1, interface.2] at carrierOutside endpoint
    exact
      retainedCarrierClausePosition_ne_variable_of_boundary
        wellFormed degree isLocal linkMem carrierClauseMember
        atomMember otherRoutesMatch
        (occurrence.sourceTerminal formula).duplicatorArm.carrierPort
        (routedClauseOrigin formula site)
        carrierOutside
        (drawingPlanarSATRoutedClauseIncidenceDrawing_routePoints_insideCarrierBoundary
          formula site
          (occurrence.sourceTerminal formula).duplicatorArm)
        (Or.inl endpoint)
  · have interface :=
      retainedDrawingCompleteCarrierLink_second_sourceTerminalInterface
        wellFormed degree isLocal linkMem
        site occurrenceMember secondEqual
    have carrierOutside :=
      retainedDrawingPlanarSATCarrierLensIncidenceDrawing_routePoints_outsideSecond
        wellFormed degree isLocal linkMem
    have endpoint :=
      EqualityLink.add_secondCarrierMacroOrigin_portPosition
        (retainedDrawingCompleteCarrierLink_lensGeometry
          wellFormed degree isLocal linkMem)
    rw [interface.1, interface.2] at carrierOutside endpoint
    exact
      retainedCarrierClausePosition_ne_variable_of_boundary
        wellFormed degree isLocal linkMem carrierClauseMember
        atomMember otherRoutesMatch
        (occurrence.sourceTerminal formula).duplicatorArm.carrierPort
        (routedClauseOrigin formula site)
        carrierOutside
        (drawingPlanarSATRoutedClauseIncidenceDrawing_routePoints_insideCarrierBoundary
          formula site
          (occurrence.sourceTerminal formula).duplicatorArm)
        (Or.inr endpoint)

/-- A retained carrier clause avoids every variable supplied by a retained
non-carrier component. -/
theorem retainedCarrierClausePosition_ne_noncarrierVariablePosition
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (carrierMetadata otherMetadata :
      DrawingPlanarSATClauseMetadata Variable)
    (carrierValid : carrierMetadata.RetainedValid formula)
    (otherValid : otherMetadata.RetainedValid formula)
    (link : EqualityLink CarrierNode)
    (carrierComponent :
      carrierMetadata.source.component = .carrier link)
    (otherNotCarrier :
      ¬∃ otherLink,
        otherMetadata.source.component = .carrier otherLink)
    (atom : PlanarSATVariable Variable)
    (atomMember :
      atom ∈
        (otherMetadata.source.incidenceDrawing
          formula).variableVertices) :
    carrierMetadata.clause.position ≠
      drawingPlanarSATVariablePosition formula atom := by
  rcases carrierMetadata with ⟨carrierClause, carrierSource⟩
  rcases carrierSource.exists_eq_carrier_of_component_eq
      link carrierComponent with
    ⟨carrierClauseIndex, carrierSourceEq⟩
  subst carrierSource
  have carrierClauseMember :=
    (⟨carrierClause, .carrier link carrierClauseIndex⟩ :
      DrawingPlanarSATClauseMetadata Variable)
      |>.retainedLocalClauseMember
        wellFormed degree isLocal carrierValid
  have carrierBounded :=
    retainedCarrierClausePosition_bounded
      wellFormed degree isLocal carrierValid.1 carrierClauseMember
  rcases otherMetadata with ⟨otherClause, otherSource⟩
  cases otherSource with
  | carrier otherLink otherClauseIndex =>
      exact False.elim
        (otherNotCarrier ⟨otherLink, rfl⟩)
  | crossover crossing otherClauseIndex =>
      by_cases incident :
          CarrierLinkIncidentToCrossover link crossing
      · exact
          retainedCarrierClausePosition_ne_crossoverVariable_of_incident
            wellFormed degree isLocal carrierValid.1 incident
            carrierClauseMember atomMember
      · have rectanglesSeparated :
            ClosedGridRectanglesSeparated
              (drawingCompleteCarrierLinkRectangleLower
                (PeriodicCNF.incidenceGraph formula) link)
              (drawingCompleteCarrierLinkRectangleUpper
                (PeriodicCNF.incidenceGraph formula) link)
              (planarSATMacrocellRouteLower crossing.point)
              (planarSATMacrocellRouteUpper crossing.point) := by
          by_contra notSeparated
          exact incident
            (retainedDrawingCompleteCarrierLink_incidentToCrossover_of_overlap
              wellFormed degree isLocal carrierValid.1 otherValid.1
              notSeparated)
        have otherBounded :=
          EmbeddedCNFIncidenceDrawing.variablePosition_satisfies
            (drawingPlanarSATCrossoverIncidenceDrawing formula crossing)
            (drawingPlanarSATCrossoverIncidenceDrawing_routesMatch
              formula crossing)
            (drawingPlanarSATCrossoverIncidenceDrawing_routePoints_bounded
              formula crossing)
            atomMember
        exact
          ne_of_inClosedGridRectangles_of_separated
            carrierBounded otherBounded rectanglesSeparated
  | bend routeBend otherClauseIndex =>
      by_cases incident :
          CarrierLinkIncidentToRouteBend link routeBend
      · exact
          retainedCarrierClausePosition_ne_bendVariable_of_incident
            wellFormed degree isLocal carrierValid.1 otherValid.1
            incident carrierClauseMember atomMember
      · have rectanglesSeparated :
            ClosedGridRectanglesSeparated
              (drawingCompleteCarrierLinkRectangleLower
                (PeriodicCNF.incidenceGraph formula) link)
              (drawingCompleteCarrierLinkRectangleUpper
                (PeriodicCNF.incidenceGraph formula) link)
              (planarSATMacrocellRouteLower
                (routeBend.drawingPoint
                  (PeriodicCNF.incidenceGraph formula)))
              (planarSATMacrocellRouteUpper
                (routeBend.drawingPoint
                  (PeriodicCNF.incidenceGraph formula))) := by
          by_contra notSeparated
          exact incident
            (retainedDrawingCompleteCarrierLink_incidentToRouteBend_of_macrocell_overlap
              wellFormed degree isLocal carrierValid.1 otherValid.1
              notSeparated)
        have otherBounded :=
          EmbeddedCNFIncidenceDrawing.variablePosition_satisfies
            (drawingPlanarSATBendCornerIncidenceDrawing
              formula routeBend)
            (drawingPlanarSATBendCornerIncidenceDrawing_isValid
              wellFormed degree isLocal otherValid.1).1
            (drawingPlanarSATBendCornerIncidenceDrawing_routePoints_bounded
              formula routeBend)
            atomMember
        exact
          ne_of_inClosedGridRectangles_of_separated
            carrierBounded otherBounded rectanglesSeparated
  | routedClause site =>
      rcases
          (mem_drawingPlanarSATRoutedClause_variableVertices_iff
            formula site atom).mp atomMember with
        ⟨representedOccurrence, representedOccurrenceMember, atomEq⟩
      by_cases rectanglesSeparated :
          ClosedGridRectanglesSeparated
            (drawingCompleteCarrierLinkRectangleLower
              (PeriodicCNF.incidenceGraph formula) link)
            (drawingCompleteCarrierLinkRectangleUpper
              (PeriodicCNF.incidenceGraph formula) link)
            (planarSATMacrocellRouteLower
              (liftedIncidenceVertexPosition
                formula (.clause site.1) site.2))
            (planarSATMacrocellRouteUpper
              (liftedIncidenceVertexPosition
                formula (.clause site.1) site.2))
      · have otherBounded :=
          EmbeddedCNFIncidenceDrawing.variablePosition_satisfies
            (drawingPlanarSATRoutedClauseIncidenceDrawing formula site)
            (drawingPlanarSATRoutedClauseIncidenceDrawing_routesMatch
              formula wellFormed site)
            (drawingPlanarSATRoutedClauseIncidenceDrawing_routePoints_bounded
              formula site)
            atomMember
        exact
          ne_of_inClosedGridRectangles_of_separated
            carrierBounded otherBounded rectanglesSeparated
      · rcases
          retainedDrawingCompleteCarrierLink_exists_sourceOccurrence_of_clauseMacrocell_overlap
            wellFormed degree isLocal carrierValid.1 site
            representedOccurrenceMember rectanglesSeparated with
          ⟨occurrence, occurrenceMember, incident⟩
        exact
          retainedCarrierClausePosition_ne_routedClauseVariable_of_incident
            wellFormed degree isLocal carrierValid.1
            occurrenceMember incident carrierClauseMember atomMember
  | routedVariable site armIndex arm routedLink otherClauseIndex =>
      have routedLinkMember :
          routedLink ∈ routedVariableLinksAt formula site :=
        List.fst_mem_of_mem_zipIdx otherValid.2.1
      have firstNodeMem :
          routedLink.first ∈ routedVariableNodes formula site := by
        rcases List.mem_map.mp routedLinkMember with
          ⟨taggedNode, taggedNodeMem, linkEq⟩
        subst routedLink
        exact List.mem_of_mem_take
          (List.fst_mem_of_mem_zipIdx taggedNodeMem)
      rcases (mem_routedVariableNodes_iff
          formula site routedLink.first).mp firstNodeMem with
        ⟨representedOccurrence, representedOccurrenceMember, _⟩
      by_cases rectanglesSeparated :
          ClosedGridRectanglesSeparated
            (drawingCompleteCarrierLinkRectangleLower
              (PeriodicCNF.incidenceGraph formula) link)
            (drawingCompleteCarrierLinkRectangleUpper
              (PeriodicCNF.incidenceGraph formula) link)
            (planarSATMacrocellRouteLower
              (liftedIncidenceVertexPosition
                formula (.variable site.1) site.2))
            (planarSATMacrocellRouteUpper
              (liftedIncidenceVertexPosition
                formula (.variable site.1) site.2))
      · have otherRoutesMatch :=
          (⟨otherClause,
              .routedVariable site armIndex arm
                routedLink otherClauseIndex⟩ :
            DrawingPlanarSATClauseMetadata Variable)
            |>.retainedLocalDrawingRoutesMatch
              wellFormed degree isLocal otherValid
        have otherBounded :=
          EmbeddedCNFIncidenceDrawing.variablePosition_satisfies
            (drawingPlanarSATRoutedVariableIncidenceDrawing
              formula site arm routedLink)
            otherRoutesMatch
            (drawingPlanarSATRoutedVariableIncidenceDrawing_routePoints_bounded
              formula site arm routedLink)
            atomMember
        exact
          ne_of_inClosedGridRectangles_of_separated
            carrierBounded otherBounded rectanglesSeparated
      · rcases
          retainedDrawingCompleteCarrierLink_exists_targetOccurrence_of_variableMacrocell_overlap
            wellFormed degree isLocal carrierValid.1 site
            representedOccurrenceMember rectanglesSeparated with
          ⟨occurrence, occurrenceMember, incident⟩
        exact
          retainedCarrierClausePosition_ne_routedVariable_of_incident
            wellFormed degree isLocal carrierValid.1 occurrenceMember
            arm routedLink incident carrierClauseMember
            ((⟨otherClause,
                .routedVariable site armIndex arm
                  routedLink otherClauseIndex⟩ :
              DrawingPlanarSATClauseMetadata Variable)
              |>.retainedLocalDrawingRoutesMatch
                wellFormed degree isLocal otherValid)
            atomMember

/-- A clause of an earlier retained carrier lens avoids both endpoints of
the consecutive later lens. -/
theorem retainedEarlierCarrierClausePosition_ne_laterEndpoint
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
      earlier ∈ retainedDrawingCompleteCarrierLinks
        (PeriodicCNF.incidenceGraph formula))
    (laterMem :
      later ∈ retainedDrawingCompleteCarrierLinks
        (PeriodicCNF.incidenceGraph formula))
    (shared : earlier.second = later.first)
    {clause : EmbeddedClause (PlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (drawingPlanarSATCarrierFormulaAt
          (Variable := Variable) earlier).zipIdx)
    (node : CarrierNode)
    (nodeEq : node = later.first ∨ node = later.second) :
    clause.position ≠
      node.position (PeriodicCNF.incidenceGraph formula) := by
  have clausePosition :=
    carrierClause_position_eq_forward_or_backward clauseMember
  have earlierGeometry :=
    retainedDrawingCompleteCarrierLink_lensGeometry
      wellFormed degree isLocal earlierMem
  have earlierDirection :=
    retainedDrawingCompleteCarrierLink_carrierDirection_eq_axis
      wellFormed degree isLocal earlierMem
  have earlierAxis :=
    retainedDrawingCompleteCarrierLink_first_isHorizontal_iff_second
      wellFormed degree isLocal earlierMem
  have earlierClearance :=
    retainedDrawingCompleteCarrierLink_hasForwardClearance
      wellFormed degree isLocal earlierMem
  have laterClearance :=
    retainedDrawingCompleteCarrierLink_hasForwardClearance
      wellFormed degree isLocal laterMem
  by_cases horizontal : earlier.first.isHorizontal = true
  · have laterHorizontal : later.first.isHorizontal = true := by
      rw [← shared]
      exact earlierAxis.mp horizontal
    rw [if_pos horizontal] at earlierDirection
    change
      AxisDirection.between
          (earlier.first.position
            (PeriodicCNF.incidenceGraph formula))
          (earlier.second.position
            (PeriodicCNF.incidenceGraph formula)) =
        .east at earlierDirection
    rw [earlierGeometry.positions] at clausePosition
    rw [earlierDirection] at clausePosition
    unfold CarrierNode.HasForwardClearance at earlierClearance
    unfold CarrierNode.HasForwardClearance at laterClearance
    rw [if_pos horizontal] at earlierClearance
    rw [if_pos laterHorizontal] at laterClearance
    rw [shared] at earlierClearance
    rcases clausePosition with clausePosition | clausePosition <;>
      rcases nodeEq with rfl | rfl <;>
      intro equal
    all_goals
      rw [clausePosition] at equal
      simp only [AxisDirection.placePoint,
        AxisDirection.orientPoint, Cell.add] at equal
      have equalX := congrArg Prod.fst equal
      simp only at equalX
      omega
  · have laterVertical : ¬later.first.isHorizontal = true := by
      intro laterHorizontal
      apply horizontal
      exact earlierAxis.mpr (by simpa [shared] using laterHorizontal)
    rw [if_neg horizontal] at earlierDirection
    change
      AxisDirection.between
          (earlier.first.position
            (PeriodicCNF.incidenceGraph formula))
          (earlier.second.position
            (PeriodicCNF.incidenceGraph formula)) =
        .north at earlierDirection
    rw [earlierGeometry.positions] at clausePosition
    rw [earlierDirection] at clausePosition
    unfold CarrierNode.HasForwardClearance at earlierClearance
    unfold CarrierNode.HasForwardClearance at laterClearance
    rw [if_neg horizontal] at earlierClearance
    rw [if_neg laterVertical] at laterClearance
    rw [shared] at earlierClearance
    rcases clausePosition with clausePosition | clausePosition <;>
      rcases nodeEq with rfl | rfl <;>
      intro equal
    all_goals
      rw [clausePosition] at equal
      simp only [AxisDirection.placePoint,
        AxisDirection.orientPoint, Cell.add] at equal
      have equalY := congrArg Prod.snd equal
      simp only at equalY
      omega

/-- A clause of a later retained carrier lens avoids both endpoints of the
consecutive earlier lens. -/
theorem retainedLaterCarrierClausePosition_ne_earlierEndpoint
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
      earlier ∈ retainedDrawingCompleteCarrierLinks
        (PeriodicCNF.incidenceGraph formula))
    (laterMem :
      later ∈ retainedDrawingCompleteCarrierLinks
        (PeriodicCNF.incidenceGraph formula))
    (shared : earlier.second = later.first)
    {clause : EmbeddedClause (PlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (drawingPlanarSATCarrierFormulaAt
          (Variable := Variable) later).zipIdx)
    (node : CarrierNode)
    (nodeEq : node = earlier.first ∨ node = earlier.second) :
    clause.position ≠
      node.position (PeriodicCNF.incidenceGraph formula) := by
  have clausePosition :=
    carrierClause_position_eq_forward_or_backward clauseMember
  have laterGeometry :=
    retainedDrawingCompleteCarrierLink_lensGeometry
      wellFormed degree isLocal laterMem
  have laterDirection :=
    retainedDrawingCompleteCarrierLink_carrierDirection_eq_axis
      wellFormed degree isLocal laterMem
  have earlierAxis :=
    retainedDrawingCompleteCarrierLink_first_isHorizontal_iff_second
      wellFormed degree isLocal earlierMem
  have earlierClearance :=
    retainedDrawingCompleteCarrierLink_hasForwardClearance
      wellFormed degree isLocal earlierMem
  by_cases horizontal : earlier.first.isHorizontal = true
  · have laterHorizontal : later.first.isHorizontal = true := by
      rw [← shared]
      exact earlierAxis.mp horizontal
    rw [if_pos laterHorizontal] at laterDirection
    change
      AxisDirection.between
          (later.first.position
            (PeriodicCNF.incidenceGraph formula))
          (later.second.position
            (PeriodicCNF.incidenceGraph formula)) =
        .east at laterDirection
    rw [laterGeometry.positions] at clausePosition
    rw [laterDirection] at clausePosition
    unfold CarrierNode.HasForwardClearance at earlierClearance
    rw [if_pos horizontal] at earlierClearance
    rcases clausePosition with clausePosition | clausePosition <;>
      rcases nodeEq with rfl | rfl <;>
      intro equal
    all_goals
      rw [clausePosition] at equal
      rw [← shared] at equal
      simp only [AxisDirection.placePoint,
        AxisDirection.orientPoint, Cell.add] at equal
      have equalX := congrArg Prod.fst equal
      simp only at equalX
      omega
  · have laterVertical : ¬later.first.isHorizontal = true := by
      intro laterHorizontal
      apply horizontal
      exact earlierAxis.mpr (by simpa [shared] using laterHorizontal)
    rw [if_neg laterVertical] at laterDirection
    change
      AxisDirection.between
          (later.first.position
            (PeriodicCNF.incidenceGraph formula))
          (later.second.position
            (PeriodicCNF.incidenceGraph formula)) =
        .north at laterDirection
    rw [laterGeometry.positions] at clausePosition
    rw [laterDirection] at clausePosition
    unfold CarrierNode.HasForwardClearance at earlierClearance
    rw [if_neg horizontal] at earlierClearance
    rcases clausePosition with clausePosition | clausePosition <;>
      rcases nodeEq with rfl | rfl <;>
      intro equal
    all_goals
      rw [clausePosition] at equal
      rw [← shared] at equal
      simp only [AxisDirection.placePoint,
        AxisDirection.orientPoint, Cell.add] at equal
      have equalY := congrArg Prod.snd equal
      simp only at equalY
      omega

/-- A retained carrier clause avoids every variable supplied by any retained
carrier component. -/
theorem retainedCarrierClausePosition_ne_carrierVariablePosition
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (carrierMetadata otherMetadata :
      DrawingPlanarSATClauseMetadata Variable)
    (carrierValid : carrierMetadata.RetainedValid formula)
    (otherValid : otherMetadata.RetainedValid formula)
    (carrierLink otherLink : EqualityLink CarrierNode)
    (carrierComponent :
      carrierMetadata.source.component = .carrier carrierLink)
    (otherComponent :
      otherMetadata.source.component = .carrier otherLink)
    (atom : PlanarSATVariable Variable)
    (atomMember :
      atom ∈
        (otherMetadata.source.incidenceDrawing
          formula).variableVertices) :
    carrierMetadata.clause.position ≠
      drawingPlanarSATVariablePosition formula atom := by
  rcases carrierMetadata with ⟨carrierClause, carrierSource⟩
  rcases carrierSource.exists_eq_carrier_of_component_eq
      carrierLink carrierComponent with
    ⟨carrierClauseIndex, carrierSourceEq⟩
  subst carrierSource
  rcases otherMetadata with ⟨otherClause, otherSource⟩
  rcases otherSource.exists_eq_carrier_of_component_eq
      otherLink otherComponent with
    ⟨otherClauseIndex, otherSourceEq⟩
  subst otherSource
  have carrierClauseMember :=
    (⟨carrierClause, .carrier carrierLink carrierClauseIndex⟩ :
      DrawingPlanarSATClauseMetadata Variable)
      |>.retainedLocalClauseMember
        wellFormed degree isLocal carrierValid
  change
    (carrierClause, carrierClauseIndex) ∈
      (drawingPlanarSATCarrierLensIncidenceDrawing
        formula carrierLink).formula.zipIdx at carrierClauseMember
  change
    atom ∈
      (drawingPlanarSATCarrierLensIncidenceDrawing
        formula otherLink).variableVertices at atomMember
  have carrierFormulaMember := carrierClauseMember
  rw [retainedDrawingPlanarSATCarrierLensIncidenceDrawing_formula
    wellFormed degree isLocal carrierValid.1] at carrierFormulaMember
  have atomCases :=
    mem_retainedDrawingPlanarSATCarrier_variableVertices
      formula wellFormed degree isLocal otherLink otherValid.1
      atom atomMember
  rcases atomCases with rfl | rfl
  · intro positionEq
    have nodePositionEq :
        carrierClause.position =
          otherLink.first.position
            (PeriodicCNF.incidenceGraph formula) := by
      simpa [drawingPlanarSATVariablePosition] using positionEq
    by_cases linksEq : carrierLink = otherLink
    · subst otherLink
      exact
        (retainedCarrierClausePosition_ne_firstNodePosition
          wellFormed degree isLocal carrierValid.1 carrierClauseMember)
          nodePositionEq
    · have carrierBounded :=
        retainedCarrierClausePosition_bounded
          wellFormed degree isLocal carrierValid.1 carrierClauseMember
      have otherBounded :=
        EmbeddedCNFIncidenceDrawing.variablePosition_satisfies
          (drawingPlanarSATCarrierLensIncidenceDrawing
            formula otherLink)
          (retainedDrawingPlanarSATCarrierLensIncidenceDrawing_isValid
            wellFormed degree isLocal otherValid.1).1
          (retainedDrawingPlanarSATCarrierLensIncidenceDrawing_routePoints_bounded
            wellFormed degree isLocal otherValid.1)
          atomMember
      change
        InClosedGridRectangle
          (drawingCompleteCarrierLinkRectangleLower
            (PeriodicCNF.incidenceGraph formula) otherLink)
          (drawingCompleteCarrierLinkRectangleUpper
            (PeriodicCNF.incidenceGraph formula) otherLink)
          (drawingPlanarSATVariablePosition formula
            (.inl (.carrier otherLink.first))) at otherBounded
      have separatedContradiction
          (separated :
            ClosedGridRectanglesSeparated
              (drawingCompleteCarrierLinkRectangleLower
                (PeriodicCNF.incidenceGraph formula) carrierLink)
              (drawingCompleteCarrierLinkRectangleUpper
                (PeriodicCNF.incidenceGraph formula) carrierLink)
              (drawingCompleteCarrierLinkRectangleLower
                (PeriodicCNF.incidenceGraph formula) otherLink)
              (drawingCompleteCarrierLinkRectangleUpper
                (PeriodicCNF.incidenceGraph formula) otherLink)) :
          False :=
        (ne_of_inClosedGridRectangles_of_separated
          carrierBounded otherBounded separated)
          (by simpa [drawingPlanarSATVariablePosition] using positionEq)
      by_cases perpendicular :
          CarrierLinksPerpendicular carrierLink otherLink
      · exact separatedContradiction
          (retainedDrawingCompleteCarrierLink_rectanglesSeparated_of_perpendicular
            wellFormed degree isLocal carrierValid.1 otherValid.1
            perpendicular)
      · by_cases sameKey :
            carrierLink.first.carrierKey =
              otherLink.first.carrierKey
        · rcases
            retainedDrawingCompleteCarrierLinks_same_key_orderCoordinate
              wellFormed degree isLocal carrierValid.1 otherValid.1
              linksEq sameKey with
            carrierBeforeOther | otherBeforeCarrier
          · by_cases shared : carrierLink.second = otherLink.first
            · exact
                (retainedEarlierCarrierClausePosition_ne_laterEndpoint
                  wellFormed degree isLocal
                  carrierValid.1 otherValid.1 shared
                  carrierFormulaMember otherLink.first (Or.inl rfl))
                  nodePositionEq
            · exact separatedContradiction
                (retainedDrawingCompleteCarrierLinks_rectanglesSeparated_of_order_of_ne
                  wellFormed degree isLocal
                  carrierValid.1 otherValid.1
                  sameKey carrierBeforeOther shared)
          · by_cases shared : otherLink.second = carrierLink.first
            · exact
                (retainedLaterCarrierClausePosition_ne_earlierEndpoint
                  wellFormed degree isLocal
                  otherValid.1 carrierValid.1 shared
                  carrierFormulaMember otherLink.first (Or.inl rfl))
                  nodePositionEq
            · exact separatedContradiction
                ((retainedDrawingCompleteCarrierLinks_rectanglesSeparated_of_order_of_ne
                  wellFormed degree isLocal
                  otherValid.1 carrierValid.1
                  sameKey.symm otherBeforeCarrier shared).symm)
        · exact separatedContradiction
            (retainedDrawingCompleteCarrierLink_rectanglesSeparated_of_parallel_key_ne
              wellFormed degree isLocal carrierValid.1 otherValid.1
              perpendicular sameKey)
  · intro positionEq
    have nodePositionEq :
        carrierClause.position =
          otherLink.second.position
            (PeriodicCNF.incidenceGraph formula) := by
      simpa [drawingPlanarSATVariablePosition] using positionEq
    by_cases linksEq : carrierLink = otherLink
    · subst otherLink
      exact
        (retainedCarrierClausePosition_ne_secondNodePosition
          wellFormed degree isLocal carrierValid.1 carrierClauseMember)
          nodePositionEq
    · have carrierBounded :=
        retainedCarrierClausePosition_bounded
          wellFormed degree isLocal carrierValid.1 carrierClauseMember
      have otherBounded :=
        EmbeddedCNFIncidenceDrawing.variablePosition_satisfies
          (drawingPlanarSATCarrierLensIncidenceDrawing
            formula otherLink)
          (retainedDrawingPlanarSATCarrierLensIncidenceDrawing_isValid
            wellFormed degree isLocal otherValid.1).1
          (retainedDrawingPlanarSATCarrierLensIncidenceDrawing_routePoints_bounded
            wellFormed degree isLocal otherValid.1)
          atomMember
      change
        InClosedGridRectangle
          (drawingCompleteCarrierLinkRectangleLower
            (PeriodicCNF.incidenceGraph formula) otherLink)
          (drawingCompleteCarrierLinkRectangleUpper
            (PeriodicCNF.incidenceGraph formula) otherLink)
          (drawingPlanarSATVariablePosition formula
            (.inl (.carrier otherLink.second))) at otherBounded
      have separatedContradiction
          (separated :
            ClosedGridRectanglesSeparated
              (drawingCompleteCarrierLinkRectangleLower
                (PeriodicCNF.incidenceGraph formula) carrierLink)
              (drawingCompleteCarrierLinkRectangleUpper
                (PeriodicCNF.incidenceGraph formula) carrierLink)
              (drawingCompleteCarrierLinkRectangleLower
                (PeriodicCNF.incidenceGraph formula) otherLink)
              (drawingCompleteCarrierLinkRectangleUpper
                (PeriodicCNF.incidenceGraph formula) otherLink)) :
          False :=
        (ne_of_inClosedGridRectangles_of_separated
          carrierBounded otherBounded separated)
          (by simpa [drawingPlanarSATVariablePosition] using positionEq)
      by_cases perpendicular :
          CarrierLinksPerpendicular carrierLink otherLink
      · exact separatedContradiction
          (retainedDrawingCompleteCarrierLink_rectanglesSeparated_of_perpendicular
            wellFormed degree isLocal carrierValid.1 otherValid.1
            perpendicular)
      · by_cases sameKey :
            carrierLink.first.carrierKey =
              otherLink.first.carrierKey
        · rcases
            retainedDrawingCompleteCarrierLinks_same_key_orderCoordinate
              wellFormed degree isLocal carrierValid.1 otherValid.1
              linksEq sameKey with
            carrierBeforeOther | otherBeforeCarrier
          · by_cases shared : carrierLink.second = otherLink.first
            · exact
                (retainedEarlierCarrierClausePosition_ne_laterEndpoint
                  wellFormed degree isLocal
                  carrierValid.1 otherValid.1 shared
                  carrierFormulaMember otherLink.second (Or.inr rfl))
                  nodePositionEq
            · exact separatedContradiction
                (retainedDrawingCompleteCarrierLinks_rectanglesSeparated_of_order_of_ne
                  wellFormed degree isLocal
                  carrierValid.1 otherValid.1
                  sameKey carrierBeforeOther shared)
          · by_cases shared : otherLink.second = carrierLink.first
            · exact
                (retainedLaterCarrierClausePosition_ne_earlierEndpoint
                  wellFormed degree isLocal
                  otherValid.1 carrierValid.1 shared
                  carrierFormulaMember otherLink.second (Or.inr rfl))
                  nodePositionEq
            · exact separatedContradiction
                ((retainedDrawingCompleteCarrierLinks_rectanglesSeparated_of_order_of_ne
                  wellFormed degree isLocal
                  otherValid.1 carrierValid.1
                  sameKey.symm otherBeforeCarrier shared).symm)
        · exact separatedContradiction
            (retainedDrawingCompleteCarrierLink_rectanglesSeparated_of_parallel_key_ne
              wellFormed degree isLocal carrierValid.1 otherValid.1
              perpendicular sameKey)

/-- Every globally used retained variable avoids a retained carrier-clause
position. -/
theorem retainedVariablePosition_ne_carrierClausePosition
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (atom : PlanarSATVariable Variable)
    (atomMember :
      atom ∈
        (retainedDrawingPlanarSATLocalIncidenceDrawing
          formula).variableVertices)
    (carrierMetadata :
      DrawingPlanarSATClauseMetadata Variable)
    (carrierValid : carrierMetadata.RetainedValid formula)
    (carrierLink : EqualityLink CarrierNode)
    (carrierComponent :
      carrierMetadata.source.component = .carrier carrierLink) :
    drawingPlanarSATVariablePosition formula atom ≠
      carrierMetadata.clause.position := by
  rcases retainedVariable_has_localMetadata
      formula wellFormed degree isLocal atom atomMember with
    ⟨otherMetadata, _, otherValid,
      localAtomMember⟩
  by_cases otherCarrier :
      ∃ otherLink,
        otherMetadata.source.component = .carrier otherLink
  · rcases otherCarrier with ⟨otherLink, otherComponent⟩
    exact Ne.symm
      (retainedCarrierClausePosition_ne_carrierVariablePosition
        wellFormed degree isLocal carrierMetadata otherMetadata
        carrierValid otherValid carrierLink otherLink
        carrierComponent otherComponent atom localAtomMember)
  · exact Ne.symm
      (retainedCarrierClausePosition_ne_noncarrierVariablePosition
        wellFormed degree isLocal carrierMetadata otherMetadata
        carrierValid otherValid carrierLink carrierComponent
        otherCarrier atom localAtomMember)

/-- Every globally used retained variable avoids one retained metadata
clause position. -/
theorem retainedVariablePosition_ne_clausePosition
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (atom : PlanarSATVariable Variable)
    (atomMember :
      atom ∈
        (retainedDrawingPlanarSATLocalIncidenceDrawing
          formula).variableVertices)
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (valid : metadata.RetainedValid formula) :
    drawingPlanarSATVariablePosition formula atom ≠
      metadata.clause.position := by
  by_cases carrier :
      ∃ link, metadata.source.component = .carrier link
  · rcases carrier with ⟨link, componentEq⟩
    exact retainedVariablePosition_ne_carrierClausePosition
      formula wellFormed degree isLocal atom atomMember
      metadata valid link componentEq
  · exact retainedVariablePosition_ne_noncarrierClausePosition
      formula wellFormed degree isLocal atom
      (retainedDrawingPlanarSATLocalIncidenceDrawing_variableVertices_valid
        formula wellFormed degree isLocal atom atomMember)
      metadata valid carrier

/-- Variable and clause positions are disjoint in the assembled retained
incidence drawing. -/
theorem
    retainedDrawingPlanarSATLocalIncidenceDrawing_variableClauseDisjoint
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal) :
    ∀ atom ∈
        (retainedDrawingPlanarSATLocalIncidenceDrawing
          formula).variableVertices,
      ∀ clause ∈
          (retainedDrawingPlanarSATLocalIncidenceDrawing formula).formula,
        (retainedDrawingPlanarSATLocalIncidenceDrawing
          formula).variablePosition atom ≠
          clause.position := by
  intro atom atomMember clause clauseMember
  rw [retainedDrawingPlanarSATLocalIncidenceDrawing_formula,
    ← retainedDrawingPlanarSATClauseMetadata_clauses]
    at clauseMember
  rcases List.mem_map.mp clauseMember with
    ⟨metadata, metadataMember, clauseEq⟩
  subst clause
  have valid :=
    retainedDrawingPlanarSATClauseMetadata_valid
      formula metadataMember
  simpa using
    retainedVariablePosition_ne_clausePosition
      formula wellFormed degree isLocal atom atomMember
      metadata valid

end PeriodicOrthocrossing
end LeanTrominoes
