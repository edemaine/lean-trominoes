import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATCarrierClausePositions
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierCrossoverGeometry
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierBendProximity
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierTerminalComponentAllSeparation

/-!
# Separation of retained carrier and macrocell clause positions

A clause position inherits every pointwise bound satisfied by its component
routes.  If a carrier lens and a non-carrier macrocell are separated, their
clause vertices therefore lie in disjoint rectangles.  If they overlap,
existing proximity theorems make the carrier incident to that macrocell.
The two clause positions then lie on opposite sides of one carrier boundary;
their only possible common point is the shared carrier-variable port, which
local planarity excludes from the carrier's clause positions.
-/

namespace LeanTrominoes

open PlanarThreeSAT

namespace PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- A nonempty clause vertex inherits any pointwise predicate satisfied by
all routes of its incidence drawing. -/
theorem clausePosition_satisfies
    {Variable : Type*} [DecidableEq Variable]
    (drawing : EmbeddedCNFIncidenceDrawing Variable)
    (routesMatch : drawing.RoutesMatch)
    {predicate : Cell → Prop}
    (bounded : drawing.RoutePointsSatisfy predicate)
    {clause : EmbeddedClause Variable}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ drawing.formula.zipIdx)
    (nonempty : clause.literals ≠ []) :
    predicate clause.position := by
  cases literalsEq : clause.literals with
  | nil => exact (nonempty literalsEq).elim
  | cons literal rest =>
      have literalMember :
          (literal, 0) ∈ clause.literals.zipIdx := by
        simp [literalsEq]
      have endpoints :=
        drawing.physicalRoutesMatch routesMatch
          clause clauseIndex clauseMember literal 0 literalMember
      have positionMember :
          clause.position ∈ drawing.routes clauseIndex 0 :=
        List.mem_of_mem_head? (by simp [endpoints.1])
      exact bounded.of_members
        clauseMember literalMember positionMember

end PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

namespace PeriodicOrthocrossing

set_option maxHeartbeats 1200000

/-- Every clause of a retained carrier equality lens is nonempty. -/
theorem retainedCarrierClause_literals_ne_nil
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
    {clause : EmbeddedClause (PlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (drawingPlanarSATCarrierLensIncidenceDrawing
          formula link).formula.zipIdx) :
    clause.literals ≠ [] := by
  have sourceMember := clauseMember
  rw [retainedDrawingPlanarSATCarrierLensIncidenceDrawing_formula
    wellFormed degree isLocal linkMem] at sourceMember
  simp [drawingPlanarSATCarrierFormulaAt, equalityInstance,
    EmbeddedClause.rename, EmbeddedClause.map] at sourceMember
  rcases sourceMember with ⟨clauseEq, _⟩ | ⟨clauseEq, _⟩ <;>
    rw [clauseEq] <;> simp

/-- A retained carrier clause does not occupy its lens's first variable
position. -/
theorem retainedCarrierClausePosition_ne_firstNodePosition
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
    {clause : EmbeddedClause (PlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (drawingPlanarSATCarrierLensIncidenceDrawing
          formula link).formula.zipIdx) :
    clause.position ≠
      link.first.position (PeriodicCNF.incidenceGraph formula) := by
  have variableMem :
      planarSATCarrierVariableMap link.first ∈
        (drawingPlanarSATCarrierLensIncidenceDrawing
          formula link).variableVertices := by
    rw [EmbeddedCNFIncidenceDrawing.variableVertices,
      retainedDrawingPlanarSATCarrierLensIncidenceDrawing_formula
        wellFormed degree isLocal linkMem]
    simp [drawingPlanarSATCarrierFormulaAt, equalityInstance,
      EmbeddedClause.rename, EmbeddedClause.map,
      planarSATCarrierVariableMap, planarSATCoreVariableMap]
  have distinct :=
    EmbeddedCNFIncidenceDrawing.variablePosition_ne_clausePosition_of_isPlanar
      (retainedDrawingPlanarSATCarrierLensIncidenceDrawing_isValid
        wellFormed degree isLocal linkMem).2.2
      variableMem
      (List.fst_mem_of_mem_zipIdx clauseMember)
  intro equal
  apply distinct
  change
    drawingPlanarSATVariablePosition formula
        (planarSATCarrierVariableMap link.first) =
      clause.position
  rw [planarSATCarrierVariableMap_position]
  exact equal.symm

/-- A retained carrier clause does not occupy its lens's second variable
position. -/
theorem retainedCarrierClausePosition_ne_secondNodePosition
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
    {clause : EmbeddedClause (PlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (drawingPlanarSATCarrierLensIncidenceDrawing
          formula link).formula.zipIdx) :
    clause.position ≠
      link.second.position (PeriodicCNF.incidenceGraph formula) := by
  have variableMem :
      planarSATCarrierVariableMap link.second ∈
        (drawingPlanarSATCarrierLensIncidenceDrawing
          formula link).variableVertices := by
    rw [EmbeddedCNFIncidenceDrawing.variableVertices,
      retainedDrawingPlanarSATCarrierLensIncidenceDrawing_formula
        wellFormed degree isLocal linkMem]
    simp [drawingPlanarSATCarrierFormulaAt, equalityInstance,
      EmbeddedClause.rename, EmbeddedClause.map,
      planarSATCarrierVariableMap, planarSATCoreVariableMap]
  have distinct :=
    EmbeddedCNFIncidenceDrawing.variablePosition_ne_clausePosition_of_isPlanar
      (retainedDrawingPlanarSATCarrierLensIncidenceDrawing_isValid
        wellFormed degree isLocal linkMem).2.2
      variableMem
      (List.fst_mem_of_mem_zipIdx clauseMember)
  intro equal
  apply distinct
  change
    drawingPlanarSATVariablePosition formula
        (planarSATCarrierVariableMap link.second) =
      clause.position
  rw [planarSATCarrierVariableMap_position]
  exact equal.symm

/-- Opposite-side component bounds separate a carrier clause from a nonempty
clause whenever their unique boundary point is one of the carrier lens's
variable endpoints. -/
theorem retainedCarrierClausePosition_ne_other_of_boundary
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
    (otherRoutesMatch : otherDrawing.RoutesMatch)
    {otherClause :
      EmbeddedClause (PlanarSATVariable Variable)}
    {otherClauseIndex : Nat}
    (otherClauseMember :
      (otherClause, otherClauseIndex) ∈
        otherDrawing.formula.zipIdx)
    (otherNonempty : otherClause.literals ≠ [])
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
    carrierClause.position ≠ otherClause.position := by
  have carrierOutsideAt :=
    EmbeddedCNFIncidenceDrawing.clausePosition_satisfies
      (drawingPlanarSATCarrierLensIncidenceDrawing formula link)
      (retainedDrawingPlanarSATCarrierLensIncidenceDrawing_isValid
        wellFormed degree isLocal linkMem).1
      carrierOutside carrierClauseMember
      (retainedCarrierClause_literals_ne_nil
        wellFormed degree isLocal linkMem carrierClauseMember)
  have otherInsideAt :=
    EmbeddedCNFIncidenceDrawing.clausePosition_satisfies
      otherDrawing otherRoutesMatch otherInside
      otherClauseMember otherNonempty
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

/-- An incident retained lens and crossover have distinct clause positions. -/
theorem retainedCarrierClausePosition_ne_crossoverClause_of_incident
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
    {otherClause :
      EmbeddedClause (PlanarSATVariable Variable)}
    {otherClauseIndex : Nat}
    (otherClauseMember :
      (otherClause, otherClauseIndex) ∈
        (drawingPlanarSATCrossoverIncidenceDrawing
          formula crossing).formula.zipIdx)
    (otherNonempty : otherClause.literals ≠ []) :
    carrierClause.position ≠ otherClause.position := by
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
      retainedCarrierClausePosition_ne_other_of_boundary
        wellFormed degree isLocal linkMem carrierClauseMember
        (drawingPlanarSATCrossoverIncidenceDrawing_routesMatch
          formula crossing)
        otherClauseMember otherNonempty
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
      retainedCarrierClausePosition_ne_other_of_boundary
        wellFormed degree isLocal linkMem carrierClauseMember
        (drawingPlanarSATCrossoverIncidenceDrawing_routesMatch
          formula crossing)
        otherClauseMember otherNonempty
        side.carrierPort (crossingMacroOrigin crossing)
        carrierOutside
        (drawingPlanarSATCrossoverIncidenceDrawing_routePoints_insideCarrierBoundary
          formula crossing side)
        (Or.inr endpoint)

/-- An incident retained lens and bend corner have distinct clause positions. -/
theorem retainedCarrierClausePosition_ne_bendClause_of_incident
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
    {otherClause :
      EmbeddedClause (PlanarSATVariable Variable)}
    {otherClauseIndex : Nat}
    (otherClauseMember :
      (otherClause, otherClauseIndex) ∈
        (drawingPlanarSATBendCornerIncidenceDrawing
          formula routeBend).formula.zipIdx)
    (otherNonempty : otherClause.literals ≠ []) :
    carrierClause.position ≠ otherClause.position := by
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
      retainedCarrierClausePosition_ne_other_of_boundary
        wellFormed degree isLocal linkMem carrierClauseMember
        otherRoutesMatch otherClauseMember otherNonempty
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
      retainedCarrierClausePosition_ne_other_of_boundary
        wellFormed degree isLocal linkMem carrierClauseMember
        otherRoutesMatch otherClauseMember otherNonempty
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
      retainedCarrierClausePosition_ne_other_of_boundary
        wellFormed degree isLocal linkMem carrierClauseMember
        otherRoutesMatch otherClauseMember otherNonempty
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
      retainedCarrierClausePosition_ne_other_of_boundary
        wellFormed degree isLocal linkMem carrierClauseMember
        otherRoutesMatch otherClauseMember otherNonempty
        routeBend.outgoingPort
        (Cell.scale planarMacroScale (routeBend.drawingPoint graph))
        carrierOutside
        (drawingPlanarSATBendCornerIncidenceDrawing_routePoints_insideOutgoing
          formula routeBend)
        (Or.inr endpoint)

/-- An incident retained lens and routed-variable arm have distinct clause
positions. -/
theorem retainedCarrierClausePosition_ne_routedVariableClause_of_incident
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
    {otherClause :
      EmbeddedClause (PlanarSATVariable Variable)}
    {otherClauseIndex : Nat}
    (otherClauseMember :
      (otherClause, otherClauseIndex) ∈
        (drawingPlanarSATRoutedVariableIncidenceDrawing
          formula site drawingArm routedLink).formula.zipIdx)
    (otherNonempty : otherClause.literals ≠ []) :
    carrierClause.position ≠ otherClause.position := by
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
      retainedCarrierClausePosition_ne_other_of_boundary
        wellFormed degree isLocal linkMem carrierClauseMember
        otherRoutesMatch otherClauseMember otherNonempty
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
      retainedCarrierClausePosition_ne_other_of_boundary
        wellFormed degree isLocal linkMem carrierClauseMember
        otherRoutesMatch otherClauseMember otherNonempty
        (occurrence.targetTerminal formula).duplicatorArm.carrierPort
        (routedVariableOrigin formula site)
        carrierOutside
        (drawingPlanarSATRoutedVariableIncidenceDrawing_routePoints_insideCarrierBoundaryAtArm
          formula site drawingArm
          (occurrence.targetTerminal formula).duplicatorArm
          routedLink)
        (Or.inr endpoint)

/-- An incident retained lens and routed source clause have distinct clause
positions. -/
theorem retainedCarrierClausePosition_ne_routedClause_of_incident
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
    {otherClause :
      EmbeddedClause (PlanarSATVariable Variable)}
    {otherClauseIndex : Nat}
    (otherClauseMember :
      (otherClause, otherClauseIndex) ∈
        (drawingPlanarSATRoutedClauseIncidenceDrawing
          formula site).formula.zipIdx)
    (otherNonempty : otherClause.literals ≠ []) :
    carrierClause.position ≠ otherClause.position := by
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
      retainedCarrierClausePosition_ne_other_of_boundary
        wellFormed degree isLocal linkMem carrierClauseMember
        otherRoutesMatch otherClauseMember otherNonempty
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
      retainedCarrierClausePosition_ne_other_of_boundary
        wellFormed degree isLocal linkMem carrierClauseMember
        otherRoutesMatch otherClauseMember otherNonempty
        (occurrence.sourceTerminal formula).duplicatorArm.carrierPort
        (routedClauseOrigin formula site)
        carrierOutside
        (drawingPlanarSATRoutedClauseIncidenceDrawing_routePoints_insideCarrierBoundary
          formula site
          (occurrence.sourceTerminal formula).duplicatorArm)
        (Or.inr endpoint)

/-- A retained carrier clause cannot occupy the clause position of a
retained non-carrier component. -/
theorem retainedCarrierClausePosition_ne_noncarrierClausePosition
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (first second : DrawingPlanarSATClauseMetadata Variable)
    (firstValid : first.RetainedValid formula)
    (secondValid : second.RetainedValid formula)
    (link : EqualityLink CarrierNode)
    (firstCarrier :
      first.source.component = .carrier link)
    (secondNotCarrier :
      ¬∃ otherLink, second.source.component = .carrier otherLink)
    (secondNonempty : second.clause.literals ≠ []) :
    first.clause.position ≠ second.clause.position := by
  rcases first with ⟨firstClause, firstSource⟩
  rcases firstSource.exists_eq_carrier_of_component_eq
      link firstCarrier with
    ⟨firstClauseIndex, firstSourceEq⟩
  subst firstSource
  have firstClauseMember :=
    (⟨firstClause, .carrier link firstClauseIndex⟩ :
      DrawingPlanarSATClauseMetadata Variable)
      |>.retainedLocalClauseMember
        wellFormed degree isLocal firstValid
  have firstBounded :=
    retainedCarrierClausePosition_bounded
      wellFormed degree isLocal firstValid.1 firstClauseMember
  rcases second with ⟨secondClause, secondSource⟩
  cases secondSource with
  | carrier secondLink secondClauseIndex =>
      exact False.elim
        (secondNotCarrier ⟨secondLink, rfl⟩)
  | crossover crossing secondClauseIndex =>
      have secondClauseMember :=
        (⟨secondClause, .crossover crossing secondClauseIndex⟩ :
          DrawingPlanarSATClauseMetadata Variable)
          |>.retainedLocalClauseMember
            wellFormed degree isLocal secondValid
      by_cases incident :
          CarrierLinkIncidentToCrossover link crossing
      · exact
          retainedCarrierClausePosition_ne_crossoverClause_of_incident
            wellFormed degree isLocal firstValid.1 incident
            firstClauseMember secondClauseMember secondNonempty
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
              wellFormed degree isLocal firstValid.1 secondValid.1
              notSeparated)
        have secondBounded :=
          EmbeddedCNFIncidenceDrawing.clausePosition_satisfies
            (drawingPlanarSATCrossoverIncidenceDrawing formula crossing)
            (drawingPlanarSATCrossoverIncidenceDrawing_routesMatch
              formula crossing)
            (drawingPlanarSATCrossoverIncidenceDrawing_routePoints_bounded
              formula crossing)
            secondClauseMember secondNonempty
        exact
          ne_of_inClosedGridRectangles_of_separated
            firstBounded secondBounded rectanglesSeparated
  | bend routeBend secondClauseIndex =>
      have secondClauseMember :=
        (⟨secondClause, .bend routeBend secondClauseIndex⟩ :
          DrawingPlanarSATClauseMetadata Variable)
          |>.retainedLocalClauseMember
            wellFormed degree isLocal secondValid
      by_cases incident :
          CarrierLinkIncidentToRouteBend link routeBend
      · exact
          retainedCarrierClausePosition_ne_bendClause_of_incident
            wellFormed degree isLocal firstValid.1 secondValid.1
            incident firstClauseMember secondClauseMember secondNonempty
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
              wellFormed degree isLocal firstValid.1 secondValid.1
              notSeparated)
        have secondBounded :=
          EmbeddedCNFIncidenceDrawing.clausePosition_satisfies
            (drawingPlanarSATBendCornerIncidenceDrawing formula routeBend)
            (drawingPlanarSATBendCornerIncidenceDrawing_isValid
              wellFormed degree isLocal secondValid.1).1
            (drawingPlanarSATBendCornerIncidenceDrawing_routePoints_bounded
              formula routeBend)
            secondClauseMember secondNonempty
        exact
          ne_of_inClosedGridRectangles_of_separated
            firstBounded secondBounded rectanglesSeparated
  | routedClause site =>
      have secondClauseMember :=
        (⟨secondClause, .routedClause site⟩ :
          DrawingPlanarSATClauseMetadata Variable)
          |>.retainedLocalClauseMember
            wellFormed degree isLocal secondValid
      have representedOccurrence :
          ∃ occurrence,
            occurrence ∈ clauseRouteOccurrencesAt formula site := by
        cases literalsEq : secondClause.literals with
        | nil => exact (secondNonempty literalsEq).elim
        | cons literal rest =>
            have literalMember :
                (literal, 0) ∈ secondClause.literals.zipIdx := by
              simp [literalsEq]
            have literalAtSite :
                (literal, 0) ∈
                  ((routedClauseAt formula site).rename
                    planarSATExternalVariableMap).literals.zipIdx := by
              have clauseEq :
                  secondClause =
                    (routedClauseAt formula site).rename
                      planarSATExternalVariableMap :=
                secondValid.2
              rw [clauseEq] at literalMember
              exact literalMember
            exact
              exists_clauseRouteOccurrence_of_routedClauseLiteralMember
                formula site literalAtSite
      rcases representedOccurrence with
        ⟨representedOccurrence, representedOccurrenceMember⟩
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
      · have secondBounded :=
          EmbeddedCNFIncidenceDrawing.clausePosition_satisfies
            (drawingPlanarSATRoutedClauseIncidenceDrawing formula site)
            (drawingPlanarSATRoutedClauseIncidenceDrawing_routesMatch
              formula wellFormed site)
            (drawingPlanarSATRoutedClauseIncidenceDrawing_routePoints_bounded
              formula site)
            secondClauseMember secondNonempty
        exact
          ne_of_inClosedGridRectangles_of_separated
            firstBounded secondBounded rectanglesSeparated
      · rcases
          retainedDrawingCompleteCarrierLink_exists_sourceOccurrence_of_clauseMacrocell_overlap
            wellFormed degree isLocal firstValid.1 site
            representedOccurrenceMember rectanglesSeparated with
          ⟨occurrence, occurrenceMember, incident⟩
        exact
          retainedCarrierClausePosition_ne_routedClause_of_incident
            wellFormed degree isLocal firstValid.1
            occurrenceMember incident firstClauseMember
            secondClauseMember secondNonempty
  | routedVariable site armIndex arm routedLink secondClauseIndex =>
      have secondClauseMember :=
        (⟨secondClause,
            .routedVariable site armIndex arm
              routedLink secondClauseIndex⟩ :
          DrawingPlanarSATClauseMetadata Variable)
          |>.retainedLocalClauseMember
            wellFormed degree isLocal secondValid
      have routedLinkMember :
          routedLink ∈ routedVariableLinksAt formula site :=
        List.fst_mem_of_mem_zipIdx secondValid.2.1
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
      · have secondBounded :=
          EmbeddedCNFIncidenceDrawing.clausePosition_satisfies
            (drawingPlanarSATRoutedVariableIncidenceDrawing
              formula site arm routedLink)
            ((⟨secondClause,
                .routedVariable site armIndex arm
                  routedLink secondClauseIndex⟩ :
              DrawingPlanarSATClauseMetadata Variable)
              |>.retainedLocalDrawingRoutesMatch
                wellFormed degree isLocal secondValid)
            (drawingPlanarSATRoutedVariableIncidenceDrawing_routePoints_bounded
              formula site arm routedLink)
            secondClauseMember secondNonempty
        exact
          ne_of_inClosedGridRectangles_of_separated
            firstBounded secondBounded rectanglesSeparated
      · rcases
          retainedDrawingCompleteCarrierLink_exists_targetOccurrence_of_variableMacrocell_overlap
            wellFormed degree isLocal firstValid.1 site
            representedOccurrenceMember rectanglesSeparated with
          ⟨occurrence, occurrenceMember, incident⟩
        exact
          retainedCarrierClausePosition_ne_routedVariableClause_of_incident
            wellFormed degree isLocal firstValid.1 occurrenceMember
            arm routedLink incident firstClauseMember
            ((⟨secondClause,
                .routedVariable site armIndex arm
                  routedLink secondClauseIndex⟩ :
              DrawingPlanarSATClauseMetadata Variable)
              |>.retainedLocalDrawingRoutesMatch
                wellFormed degree isLocal secondValid)
            secondClauseMember secondNonempty

end PeriodicOrthocrossing
end LeanTrominoes
