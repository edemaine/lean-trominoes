/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierTerminalComponentProximity

/-!
# Separation of retained carriers from all routed terminal components

A variable-arm route stays inside each of the west, north, and east
macrocell boundaries, not just the boundary carrying that arm's own terminal.
Thus a retained carrier incident to any terminal at the same routed variable
site avoids every active arm there.  Together with macrocell separation, this
discharges all selected carrier/routed-variable and carrier/routed-clause
pairs.
-/

namespace LeanTrominoes

namespace PlanarThreeSAT

/-- Every active duplicator-arm route lies inside the carrier boundary at
each of the three possible external fanout ports. -/
theorem
    duplicatorArmStraightIncidenceDrawing_routePoints_insideCarrierBoundaryAtArm
    (drawingArm boundaryArm : DuplicatorArm) :
    (duplicatorArmStraightIncidenceDrawing drawingArm).RoutePointsSatisfy
      boundaryArm.carrierPort.InsideCarrierBoundary := by
  cases drawingArm <;> cases boundaryArm <;> native_decide

/-- Contact of an active arm with any external fanout port is endpoint-only
(and is vacuous when that arm does not use the port). -/
theorem
    duplicatorArmStraightIncidenceDrawing_routeContactsAt_carrierPortAtArm
    (drawingArm boundaryArm : DuplicatorArm) :
    (duplicatorArmStraightIncidenceDrawing drawingArm).RouteContactsAtEndpoint
      boundaryArm.carrierPort.position := by
  exact
    EmbeddedCNFIncidenceDrawing.straightIncidenceDrawing_routeContactsAtEndpoint
      (duplicatorArmFormula drawingArm)
      (DuplicatorArmVariable.position drawingArm)
      boundaryArm.carrierPort.position

/-- Translation preserves containment inside any selected external arm
boundary. -/
theorem
    duplicatorArmStraightIncidenceDrawing_translate_routePoints_insideCarrierBoundaryAtArm
    (drawingArm boundaryArm : DuplicatorArm) (origin : Cell) :
    ((duplicatorArmStraightIncidenceDrawing drawingArm).translate origin)
      |>.RoutePointsSatisfy
        (boundaryArm.carrierPort.InsideCarrierBoundaryAt origin) := by
  exact
    (duplicatorArmStraightIncidenceDrawing_routePoints_insideCarrierBoundaryAtArm
      drawingArm boundaryArm).translate origin
        (fun point inside =>
          boundaryArm.carrierPort.insideCarrierBoundaryAt_add
            origin point inside)

/-- Translation preserves endpoint-only contact with any selected external
arm port. -/
theorem
    duplicatorArmStraightIncidenceDrawing_translate_routeContactsAt_carrierPortAtArm
    (drawingArm boundaryArm : DuplicatorArm) (origin : Cell) :
    ((duplicatorArmStraightIncidenceDrawing drawingArm).translate origin)
      |>.RouteContactsAtEndpoint
        (Cell.add origin boundaryArm.carrierPort.position) := by
  exact
    (duplicatorArmStraightIncidenceDrawing_routeContactsAt_carrierPortAtArm
      drawingArm boundaryArm).translate origin

end PlanarThreeSAT

namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 1200000

/-- A placed routed-variable arm stays inside the carrier boundary belonging
to any represented terminal arm at the same macrocell. -/
theorem
    drawingPlanarSATRoutedVariableIncidenceDrawing_routePoints_insideCarrierBoundaryAtArm
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : VariableRouteSite Variable)
    (drawingArm boundaryArm : DuplicatorArm)
    (link : EqualityLink (PlanarSATNode Variable)) :
    (drawingPlanarSATRoutedVariableIncidenceDrawing
      formula site drawingArm link).RoutePointsSatisfy
        (boundaryArm.carrierPort.InsideCarrierBoundaryAt
          (routedVariableOrigin formula site)) := by
  unfold drawingPlanarSATRoutedVariableIncidenceDrawing
  exact
    (duplicatorArmStraightIncidenceDrawing_translate_routePoints_insideCarrierBoundaryAtArm
      drawingArm boundaryArm
      (routedVariableOrigin formula site)).rename _ _

/-- A placed routed-variable arm has endpoint-only contact with every
possible external fanout port. -/
theorem
    drawingPlanarSATRoutedVariableIncidenceDrawing_routeContactsAt_carrierPortAtArm
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : VariableRouteSite Variable)
    (drawingArm boundaryArm : DuplicatorArm)
    (link : EqualityLink (PlanarSATNode Variable)) :
    (drawingPlanarSATRoutedVariableIncidenceDrawing
      formula site drawingArm link).RouteContactsAtEndpoint
        (Cell.add
          (routedVariableOrigin formula site)
          boundaryArm.carrierPort.position) := by
  unfold drawingPlanarSATRoutedVariableIncidenceDrawing
  exact
    (duplicatorArmStraightIncidenceDrawing_translate_routeContactsAt_carrierPortAtArm
      drawingArm boundaryArm
      (routedVariableOrigin formula site)).rename _ _

/-- Genuine routes of a raw retained lens avoid routes of any active
variable arm at a macrocell incident to that lens. -/
theorem
    retainedDrawingPlanarSATCarrierRoutedVariableRoutesAvoidEachOther_of_raw_incidentAtSite
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    {carrierLink : EqualityLink CarrierNode}
    (carrierLinkMember :
      carrierLink ∈ retainedDrawingCompleteCarrierLinksRaw
        (PeriodicCNF.incidenceGraph formula))
    {site : VariableRouteSite Variable}
    {occurrence : CNFRouteOccurrence Variable}
    (occurrenceMember :
      occurrence ∈ variableRouteOccurrencesAt formula site)
    (drawingArm : DuplicatorArm)
    (routedLink : EqualityLink (PlanarSATNode Variable))
    (incident :
      CarrierLinkIncidentToTargetTerminal
        formula carrierLink occurrence)
    {carrierClause :
      EmbeddedClause (PlanarSATVariable Variable)}
    {carrierClauseIndex : Nat}
    (carrierClauseMember :
      (carrierClause, carrierClauseIndex) ∈
        (drawingPlanarSATCarrierLensIncidenceDrawing
          formula carrierLink).formula.zipIdx)
    {carrierLiteral : PlanarSATVariable Variable × Bool}
    {carrierLiteralIndex : Nat}
    (carrierLiteralMember :
      (carrierLiteral, carrierLiteralIndex) ∈
        carrierClause.literals.zipIdx)
    {routedClause :
      EmbeddedClause (PlanarSATVariable Variable)}
    {routedClauseIndex : Nat}
    (routedClauseMember :
      (routedClause, routedClauseIndex) ∈
        (drawingPlanarSATRoutedVariableIncidenceDrawing
          formula site drawingArm routedLink).formula.zipIdx)
    {routedLiteral : PlanarSATVariable Variable × Bool}
    {routedLiteralIndex : Nat}
    (routedLiteralMember :
      (routedLiteral, routedLiteralIndex) ∈
        routedClause.literals.zipIdx) :
    EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
      ((drawingPlanarSATCarrierLensIncidenceDrawing
        formula carrierLink).routes
          carrierClauseIndex carrierLiteralIndex)
      ((drawingPlanarSATRoutedVariableIncidenceDrawing
        formula site drawingArm routedLink).routes
          routedClauseIndex routedLiteralIndex) := by
  rcases incident with firstEqual | secondEqual
  · have interface :=
      retainedDrawingCompleteCarrierLinkRaw_first_targetTerminalInterface
        wellFormed degree isLocal carrierLinkMember
        site occurrenceMember firstEqual
    have carrierBounded :=
      retainedDrawingPlanarSATCarrierLensIncidenceDrawing_routePoints_outsideFirst_of_raw
        wellFormed degree isLocal carrierLinkMember
    have carrierContacts :=
      retainedDrawingPlanarSATCarrierLensIncidenceDrawing_routeContactsAt_first_of_raw
        wellFormed degree isLocal carrierLinkMember
    rw [interface.1, interface.2] at carrierBounded carrierContacts
    exact
      drawingRoutesAvoidEachOther_of_members_of_outside_insideCarrierBoundaryAt
        (occurrence.targetTerminal formula).duplicatorArm.carrierPort
        (routedVariableOrigin formula site)
        carrierBounded
        (drawingPlanarSATRoutedVariableIncidenceDrawing_routePoints_insideCarrierBoundaryAtArm
          formula site drawingArm
          (occurrence.targetTerminal formula).duplicatorArm
          routedLink)
        carrierContacts
        (drawingPlanarSATRoutedVariableIncidenceDrawing_routeContactsAt_carrierPortAtArm
          formula site drawingArm
          (occurrence.targetTerminal formula).duplicatorArm
          routedLink)
        carrierClauseMember carrierLiteralMember
        routedClauseMember routedLiteralMember
  · have interface :=
      retainedDrawingCompleteCarrierLinkRaw_second_targetTerminalInterface
        wellFormed degree isLocal carrierLinkMember
        site occurrenceMember secondEqual
    have carrierBounded :=
      retainedDrawingPlanarSATCarrierLensIncidenceDrawing_routePoints_outsideSecond_of_raw
        wellFormed degree isLocal carrierLinkMember
    have carrierContacts :=
      retainedDrawingPlanarSATCarrierLensIncidenceDrawing_routeContactsAt_second_of_raw
        wellFormed degree isLocal carrierLinkMember
    rw [interface.1, interface.2] at carrierBounded carrierContacts
    exact
      drawingRoutesAvoidEachOther_of_members_of_outside_insideCarrierBoundaryAt
        (occurrence.targetTerminal formula).duplicatorArm.carrierPort
        (routedVariableOrigin formula site)
        carrierBounded
        (drawingPlanarSATRoutedVariableIncidenceDrawing_routePoints_insideCarrierBoundaryAtArm
          formula site drawingArm
          (occurrence.targetTerminal formula).duplicatorArm
          routedLink)
        carrierContacts
        (drawingPlanarSATRoutedVariableIncidenceDrawing_routeContactsAt_carrierPortAtArm
          formula site drawingArm
          (occurrence.targetTerminal formula).duplicatorArm
          routedLink)
        carrierClauseMember carrierLiteralMember
        routedClauseMember routedLiteralMember

/-- Every raw retained carrier route whose source translate lies in the
neighbor window avoids every route of a represented routed-variable
component. -/
theorem
    retainedDrawingPlanarSATCarrierRoutedVariableRoutesAvoidEachOther_of_raw
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    {carrierLink : EqualityLink CarrierNode}
    (carrierLinkMember :
      carrierLink ∈ retainedDrawingCompleteCarrierLinksRaw
        (PeriodicCNF.incidenceGraph formula))
    (firstTranslateNeighbor :
      IsNeighborTranslation carrierLink.first.translate)
    {site : VariableRouteSite Variable}
    {drawingArm : DuplicatorArm}
    {routedLink : EqualityLink (PlanarSATNode Variable)}
    (routedLinkMember :
      routedLink ∈ routedVariableLinksAt formula site)
    {carrierClause :
      EmbeddedClause (PlanarSATVariable Variable)}
    {carrierClauseIndex : Nat}
    (carrierClauseMember :
      (carrierClause, carrierClauseIndex) ∈
        (drawingPlanarSATCarrierLensIncidenceDrawing
          formula carrierLink).formula.zipIdx)
    {carrierLiteral : PlanarSATVariable Variable × Bool}
    {carrierLiteralIndex : Nat}
    (carrierLiteralMember :
      (carrierLiteral, carrierLiteralIndex) ∈
        carrierClause.literals.zipIdx)
    {routedClause :
      EmbeddedClause (PlanarSATVariable Variable)}
    {routedClauseIndex : Nat}
    (routedClauseMember :
      (routedClause, routedClauseIndex) ∈
        (drawingPlanarSATRoutedVariableIncidenceDrawing
          formula site drawingArm routedLink).formula.zipIdx)
    {routedLiteral : PlanarSATVariable Variable × Bool}
    {routedLiteralIndex : Nat}
    (routedLiteralMember :
      (routedLiteral, routedLiteralIndex) ∈
        routedClause.literals.zipIdx) :
    EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
      ((drawingPlanarSATCarrierLensIncidenceDrawing
        formula carrierLink).routes
          carrierClauseIndex carrierLiteralIndex)
      ((drawingPlanarSATRoutedVariableIncidenceDrawing
        formula site drawingArm routedLink).routes
          routedClauseIndex routedLiteralIndex) := by
  have firstNodeMem :
      routedLink.first ∈ routedVariableNodes formula site := by
    rcases List.mem_map.mp routedLinkMember with
      ⟨taggedNode, taggedNodeMem, linkEq⟩
    subst routedLink
    exact List.mem_of_mem_take
      (List.fst_mem_of_mem_zipIdx taggedNodeMem)
  rcases (mem_routedVariableNodes_iff
      formula site routedLink.first).mp firstNodeMem with
    ⟨representedOccurrence, representedOccurrenceMem,
      _⟩
  by_cases rectanglesSeparated :
      ClosedGridRectanglesSeparated
        (drawingCompleteCarrierLinkRectangleLower
          (PeriodicCNF.incidenceGraph formula) carrierLink)
        (drawingCompleteCarrierLinkRectangleUpper
          (PeriodicCNF.incidenceGraph formula) carrierLink)
        (planarSATMacrocellRouteLower
          (liftedIncidenceVertexPosition
            formula (.variable site.1) site.2))
        (planarSATMacrocellRouteUpper
          (liftedIncidenceVertexPosition
            formula (.variable site.1) site.2))
  · exact
      retainedDrawingPlanarSATCarrierRoute_avoids_macrocell_of_raw_rectanglesSeparated
        wellFormed degree isLocal carrierLinkMember
        carrierClauseMember carrierLiteralMember
        (drawingPlanarSATRoutedVariableIncidenceDrawing_routePoints_bounded
          formula site drawingArm routedLink)
        routedClauseMember routedLiteralMember rectanglesSeparated
  · rcases
      retainedDrawingCompleteCarrierLinkRaw_exists_targetOccurrence_of_variableMacrocell_overlap
        wellFormed degree isLocal carrierLinkMember firstTranslateNeighbor site
        representedOccurrenceMem rectanglesSeparated with
      ⟨occurrence, occurrenceMember, incident⟩
    exact
      retainedDrawingPlanarSATCarrierRoutedVariableRoutesAvoidEachOther_of_raw_incidentAtSite
        wellFormed degree isLocal carrierLinkMember
        occurrenceMember drawingArm routedLink incident
        carrierClauseMember carrierLiteralMember
        routedClauseMember routedLiteralMember

/-- Every raw retained carrier route whose source translate lies in the
neighbor window avoids every route of a represented routed source-clause
component. -/
theorem
    retainedDrawingPlanarSATCarrierRoutedClauseRoutesAvoidEachOther_of_raw
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    {carrierLink : EqualityLink CarrierNode}
    (carrierLinkMember :
      carrierLink ∈ retainedDrawingCompleteCarrierLinksRaw
        (PeriodicCNF.incidenceGraph formula))
    (firstTranslateNeighbor :
      IsNeighborTranslation carrierLink.first.translate)
    {site : ClauseRouteSite}
    {representedOccurrence : CNFRouteOccurrence Variable}
    (representedOccurrenceMember :
      representedOccurrence ∈ clauseRouteOccurrencesAt formula site)
    {carrierClause :
      EmbeddedClause (PlanarSATVariable Variable)}
    {carrierClauseIndex : Nat}
    (carrierClauseMember :
      (carrierClause, carrierClauseIndex) ∈
        (drawingPlanarSATCarrierLensIncidenceDrawing
          formula carrierLink).formula.zipIdx)
    {carrierLiteral : PlanarSATVariable Variable × Bool}
    {carrierLiteralIndex : Nat}
    (carrierLiteralMember :
      (carrierLiteral, carrierLiteralIndex) ∈
        carrierClause.literals.zipIdx)
    {routedClause :
      EmbeddedClause (PlanarSATVariable Variable)}
    {routedClauseIndex : Nat}
    (routedClauseMember :
      (routedClause, routedClauseIndex) ∈
        (drawingPlanarSATRoutedClauseIncidenceDrawing
          formula site).formula.zipIdx)
    {routedLiteral : PlanarSATVariable Variable × Bool}
    {routedLiteralIndex : Nat}
    (routedLiteralMember :
      (routedLiteral, routedLiteralIndex) ∈
        routedClause.literals.zipIdx) :
    EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
      ((drawingPlanarSATCarrierLensIncidenceDrawing
        formula carrierLink).routes
          carrierClauseIndex carrierLiteralIndex)
      ((drawingPlanarSATRoutedClauseIncidenceDrawing
        formula site).routes
          routedClauseIndex routedLiteralIndex) := by
  by_cases rectanglesSeparated :
      ClosedGridRectanglesSeparated
        (drawingCompleteCarrierLinkRectangleLower
          (PeriodicCNF.incidenceGraph formula) carrierLink)
        (drawingCompleteCarrierLinkRectangleUpper
          (PeriodicCNF.incidenceGraph formula) carrierLink)
        (planarSATMacrocellRouteLower
          (liftedIncidenceVertexPosition
            formula (.clause site.1) site.2))
        (planarSATMacrocellRouteUpper
          (liftedIncidenceVertexPosition
            formula (.clause site.1) site.2))
  · exact
      retainedDrawingPlanarSATCarrierRoute_avoids_macrocell_of_raw_rectanglesSeparated
        wellFormed degree isLocal carrierLinkMember
        carrierClauseMember carrierLiteralMember
        (drawingPlanarSATRoutedClauseIncidenceDrawing_routePoints_bounded
          formula site)
        routedClauseMember routedLiteralMember rectanglesSeparated
  · rcases
      retainedDrawingCompleteCarrierLinkRaw_exists_sourceOccurrence_of_clauseMacrocell_overlap
        wellFormed degree isLocal carrierLinkMember firstTranslateNeighbor site
        representedOccurrenceMember rectanglesSeparated with
      ⟨occurrence, occurrenceMember, incident⟩
    exact
      retainedDrawingPlanarSATCarrierRoutedClauseRoutesAvoidEachOther_of_raw_incident
        wellFormed degree isLocal carrierLinkMember
        occurrenceMember incident
        carrierClauseMember carrierLiteralMember
        routedClauseMember routedLiteralMember

/-! ## Selected-representative compatibility wrappers -/

theorem
    retainedDrawingPlanarSATCarrierRoutedVariableRoutesAvoidEachOther_of_incidentAtSite
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    {carrierLink : EqualityLink CarrierNode}
    (carrierLinkMember :
      carrierLink ∈ retainedDrawingCompleteCarrierLinks
        (PeriodicCNF.incidenceGraph formula))
    {site : VariableRouteSite Variable}
    {occurrence : CNFRouteOccurrence Variable}
    (occurrenceMember :
      occurrence ∈ variableRouteOccurrencesAt formula site)
    (drawingArm : DuplicatorArm)
    (routedLink : EqualityLink (PlanarSATNode Variable))
    (incident :
      CarrierLinkIncidentToTargetTerminal
        formula carrierLink occurrence)
    {carrierClause :
      EmbeddedClause (PlanarSATVariable Variable)}
    {carrierClauseIndex : Nat}
    (carrierClauseMember :
      (carrierClause, carrierClauseIndex) ∈
        (drawingPlanarSATCarrierLensIncidenceDrawing
          formula carrierLink).formula.zipIdx)
    {carrierLiteral : PlanarSATVariable Variable × Bool}
    {carrierLiteralIndex : Nat}
    (carrierLiteralMember :
      (carrierLiteral, carrierLiteralIndex) ∈
        carrierClause.literals.zipIdx)
    {routedClause :
      EmbeddedClause (PlanarSATVariable Variable)}
    {routedClauseIndex : Nat}
    (routedClauseMember :
      (routedClause, routedClauseIndex) ∈
        (drawingPlanarSATRoutedVariableIncidenceDrawing
          formula site drawingArm routedLink).formula.zipIdx)
    {routedLiteral : PlanarSATVariable Variable × Bool}
    {routedLiteralIndex : Nat}
    (routedLiteralMember :
      (routedLiteral, routedLiteralIndex) ∈
        routedClause.literals.zipIdx) :
    EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
      ((drawingPlanarSATCarrierLensIncidenceDrawing
        formula carrierLink).routes
          carrierClauseIndex carrierLiteralIndex)
      ((drawingPlanarSATRoutedVariableIncidenceDrawing
        formula site drawingArm routedLink).routes
          routedClauseIndex routedLiteralIndex) :=
  retainedDrawingPlanarSATCarrierRoutedVariableRoutesAvoidEachOther_of_raw_incidentAtSite
    wellFormed degree isLocal
      ((mem_retainedDrawingCompleteCarrierLinks_iff
        formula.incidenceGraph carrierLink).mp carrierLinkMember).1
      occurrenceMember drawingArm routedLink incident
      carrierClauseMember carrierLiteralMember
      routedClauseMember routedLiteralMember

theorem
    retainedDrawingPlanarSATCarrierRoutedVariableRoutesAvoidEachOther
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    {carrierLink : EqualityLink CarrierNode}
    (carrierLinkMember :
      carrierLink ∈ retainedDrawingCompleteCarrierLinks
        (PeriodicCNF.incidenceGraph formula))
    {site : VariableRouteSite Variable}
    {drawingArm : DuplicatorArm}
    {routedLink : EqualityLink (PlanarSATNode Variable)}
    (routedLinkMember :
      routedLink ∈ routedVariableLinksAt formula site)
    {carrierClause :
      EmbeddedClause (PlanarSATVariable Variable)}
    {carrierClauseIndex : Nat}
    (carrierClauseMember :
      (carrierClause, carrierClauseIndex) ∈
        (drawingPlanarSATCarrierLensIncidenceDrawing
          formula carrierLink).formula.zipIdx)
    {carrierLiteral : PlanarSATVariable Variable × Bool}
    {carrierLiteralIndex : Nat}
    (carrierLiteralMember :
      (carrierLiteral, carrierLiteralIndex) ∈
        carrierClause.literals.zipIdx)
    {routedClause :
      EmbeddedClause (PlanarSATVariable Variable)}
    {routedClauseIndex : Nat}
    (routedClauseMember :
      (routedClause, routedClauseIndex) ∈
        (drawingPlanarSATRoutedVariableIncidenceDrawing
          formula site drawingArm routedLink).formula.zipIdx)
    {routedLiteral : PlanarSATVariable Variable × Bool}
    {routedLiteralIndex : Nat}
    (routedLiteralMember :
      (routedLiteral, routedLiteralIndex) ∈
        routedClause.literals.zipIdx) :
    EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
      ((drawingPlanarSATCarrierLensIncidenceDrawing
        formula carrierLink).routes
          carrierClauseIndex carrierLiteralIndex)
      ((drawingPlanarSATRoutedVariableIncidenceDrawing
        formula site drawingArm routedLink).routes
          routedClauseIndex routedLiteralIndex) :=
  retainedDrawingPlanarSATCarrierRoutedVariableRoutesAvoidEachOther_of_raw
    wellFormed degree isLocal
      ((mem_retainedDrawingCompleteCarrierLinks_iff
        formula.incidenceGraph carrierLink).mp carrierLinkMember).1
      (retainedDrawingCompleteCarrierLink_first_translate_neighbor
        formula.incidenceGraph carrierLinkMember)
      routedLinkMember carrierClauseMember carrierLiteralMember
      routedClauseMember routedLiteralMember

theorem
    retainedDrawingPlanarSATCarrierRoutedClauseRoutesAvoidEachOther
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    {carrierLink : EqualityLink CarrierNode}
    (carrierLinkMember :
      carrierLink ∈ retainedDrawingCompleteCarrierLinks
        (PeriodicCNF.incidenceGraph formula))
    {site : ClauseRouteSite}
    {representedOccurrence : CNFRouteOccurrence Variable}
    (representedOccurrenceMember :
      representedOccurrence ∈ clauseRouteOccurrencesAt formula site)
    {carrierClause :
      EmbeddedClause (PlanarSATVariable Variable)}
    {carrierClauseIndex : Nat}
    (carrierClauseMember :
      (carrierClause, carrierClauseIndex) ∈
        (drawingPlanarSATCarrierLensIncidenceDrawing
          formula carrierLink).formula.zipIdx)
    {carrierLiteral : PlanarSATVariable Variable × Bool}
    {carrierLiteralIndex : Nat}
    (carrierLiteralMember :
      (carrierLiteral, carrierLiteralIndex) ∈
        carrierClause.literals.zipIdx)
    {routedClause :
      EmbeddedClause (PlanarSATVariable Variable)}
    {routedClauseIndex : Nat}
    (routedClauseMember :
      (routedClause, routedClauseIndex) ∈
        (drawingPlanarSATRoutedClauseIncidenceDrawing
          formula site).formula.zipIdx)
    {routedLiteral : PlanarSATVariable Variable × Bool}
    {routedLiteralIndex : Nat}
    (routedLiteralMember :
      (routedLiteral, routedLiteralIndex) ∈
        routedClause.literals.zipIdx) :
    EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
      ((drawingPlanarSATCarrierLensIncidenceDrawing
        formula carrierLink).routes
          carrierClauseIndex carrierLiteralIndex)
      ((drawingPlanarSATRoutedClauseIncidenceDrawing
        formula site).routes
          routedClauseIndex routedLiteralIndex) :=
  retainedDrawingPlanarSATCarrierRoutedClauseRoutesAvoidEachOther_of_raw
    wellFormed degree isLocal
      ((mem_retainedDrawingCompleteCarrierLinks_iff
        formula.incidenceGraph carrierLink).mp carrierLinkMember).1
      (retainedDrawingCompleteCarrierLink_first_translate_neighbor
        formula.incidenceGraph carrierLinkMember)
      representedOccurrenceMember carrierClauseMember carrierLiteralMember
      routedClauseMember routedLiteralMember

end PeriodicOrthocrossing
end LeanTrominoes
