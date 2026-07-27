import LeanTrominoes.PeriodicOrthocrossingCarrierTerminalPortGeometry
import LeanTrominoes.PeriodicOrthocrossingTerminalComponentCarrierInterface

/-!
# Carrier-lens interfaces at routed clause and variable terminals

For every selected CNF-route occurrence, its source and target segment
terminals use exactly the carrier-facing compass port and macrocell origin
of the corresponding routed clause or variable component.  These identities
match either endpoint of an incident retained carrier lens with the placed
terminal drawing.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 800000

/-- A target occurrence terminal's increasing-coordinate carrier port is
the compass port of its classified duplicator arm. -/
theorem CNFRouteOccurrence.targetTerminal_carrierPort_eq_duplicatorArm
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (occurrence : CNFRouteOccurrence Variable)
    (aligned :
      (occurrence.targetTerminal formula).indexed.segment.IsAxisAligned) :
    (occurrence.targetTerminal formula).carrierPort =
      (occurrence.targetTerminal formula).duplicatorArm.carrierPort := by
  apply CornerPort.position_injective
  rw [(occurrence.targetTerminal formula).carrierPort_position aligned,
    occurrence.targetTerminal_localPosition formula,
    occurrence.targetTerminal_duplicatorArm formula,
    DuplicatorArm.carrierPort_position]

/-- A source occurrence terminal's increasing-coordinate carrier port is
the compass port of its classified duplicator arm. -/
theorem CNFRouteOccurrence.sourceTerminal_carrierPort_eq_duplicatorArm
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (occurrence : CNFRouteOccurrence Variable)
    (aligned :
      (occurrence.sourceTerminal formula).indexed.segment.IsAxisAligned) :
    (occurrence.sourceTerminal formula).carrierPort =
      (occurrence.sourceTerminal formula).duplicatorArm.carrierPort := by
  apply CornerPort.position_injective
  rw [(occurrence.sourceTerminal formula).carrierPort_position aligned,
    occurrence.sourceTerminal_localPosition formula,
    occurrence.sourceTerminal_duplicatorArm formula,
    DuplicatorArm.carrierPort_position]

/-- The scaled drawing point of a selected target terminal is the origin of
its routed-variable macrocell. -/
theorem
    CNFRouteOccurrence.targetTerminal_scaledDrawingPoint_eq_routedVariableOrigin
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (site : VariableRouteSite Variable)
    {occurrence : CNFRouteOccurrence Variable}
    (occurrenceMember :
      occurrence ∈ variableRouteOccurrencesAt formula site) :
    Cell.scale planarMacroScale
        ((occurrence.targetTerminal formula).drawingPoint
          (PeriodicCNF.incidenceGraph formula)) =
      routedVariableOrigin formula site := by
  have selected :=
    variableRouteOccurrencesAt_mem_drawing_and_variableOccurrence
      formula site occurrenceMember
  unfold routedVariableOrigin
    liftedIncidenceVertexMacroOrigin
  rw [occurrence.targetTerminal_drawingPoint_eq_lifted
    formula wellFormed selected.1, selected.2]

/-- The scaled drawing point of a selected source terminal is the origin of
its routed-clause macrocell. -/
theorem
    CNFRouteOccurrence.sourceTerminal_scaledDrawingPoint_eq_routedClauseOrigin
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (site : ClauseRouteSite)
    {occurrence : CNFRouteOccurrence Variable}
    (occurrenceMember :
      occurrence ∈ clauseRouteOccurrencesAt formula site) :
    Cell.scale planarMacroScale
        ((occurrence.sourceTerminal formula).drawingPoint
          (PeriodicCNF.incidenceGraph formula)) =
      routedClauseOrigin formula site := by
  have edgeMember :
      (occurrence.edge, occurrence.edgeIndex) ∈
        (PeriodicCNF.incidenceGraph formula).edges.zipIdx := by
    rcases List.mem_map.mp occurrenceMember with
      ⟨taggedIncidence, taggedIncidenceMember, occurrenceEqual⟩
    subst occurrence
    exact PeriodicCNF.tagged_incidence_edge_mem
      formula (List.mem_filter.mp taggedIncidenceMember).1
  have siteEqual :=
    clauseRouteOccurrencesAt_clauseOccurrence
      formula site occurrenceMember
  unfold routedClauseOrigin
    liftedIncidenceVertexMacroOrigin
  rw [CNFRouteOccurrence.sourceTerminal_drawingPoint_eq_lifted
    formula wellFormed occurrence edgeMember, siteEqual]

/-- If a retained carrier starts at a selected target terminal, its first
boundary interface is exactly the routed-variable arm interface. -/
theorem drawingCompleteCarrierLink_first_targetTerminalInterface
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMember :
      link ∈ drawingCompleteCarrierLinks
        (PeriodicCNF.incidenceGraph formula))
    (site : VariableRouteSite Variable)
    {occurrence : CNFRouteOccurrence Variable}
    (occurrenceMember :
      occurrence ∈ variableRouteOccurrencesAt formula site)
    (endpointEqual :
      link.first =
        .terminal (occurrence.targetTerminal formula)) :
    EqualityLink.firstCarrierPort
          (CarrierNode.position
            (PeriodicCNF.incidenceGraph formula)) link =
        (occurrence.targetTerminal formula).duplicatorArm.carrierPort ∧
      EqualityLink.firstCarrierMacroOrigin
          (CarrierNode.position
            (PeriodicCNF.incidenceGraph formula)) link =
        routedVariableOrigin formula site := by
  have aligned :=
    drawingCompleteCarrierLink_terminal_axisAligned
      wellFormed degree isLocal linkMember (Or.inl endpointEqual)
  constructor
  · exact
      (drawingCompleteCarrierLink_firstCarrierPort_eq_terminal
        wellFormed degree isLocal linkMember endpointEqual).trans
        (occurrence.targetTerminal_carrierPort_eq_duplicatorArm
          formula aligned)
  · exact
      (drawingCompleteCarrierLink_firstCarrierMacroOrigin_eq_terminal
        wellFormed degree isLocal linkMember endpointEqual).trans
        (occurrence.targetTerminal_scaledDrawingPoint_eq_routedVariableOrigin
          formula wellFormed site occurrenceMember)

/-- If a retained carrier ends at a selected target terminal, its second
boundary interface is exactly the routed-variable arm interface. -/
theorem drawingCompleteCarrierLink_second_targetTerminalInterface
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMember :
      link ∈ drawingCompleteCarrierLinks
        (PeriodicCNF.incidenceGraph formula))
    (site : VariableRouteSite Variable)
    {occurrence : CNFRouteOccurrence Variable}
    (occurrenceMember :
      occurrence ∈ variableRouteOccurrencesAt formula site)
    (endpointEqual :
      link.second =
        .terminal (occurrence.targetTerminal formula)) :
    EqualityLink.secondCarrierPort
          (CarrierNode.position
            (PeriodicCNF.incidenceGraph formula)) link =
        (occurrence.targetTerminal formula).duplicatorArm.carrierPort ∧
      EqualityLink.secondCarrierMacroOrigin
          (CarrierNode.position
            (PeriodicCNF.incidenceGraph formula)) link =
        routedVariableOrigin formula site := by
  have aligned :=
    drawingCompleteCarrierLink_terminal_axisAligned
      wellFormed degree isLocal linkMember (Or.inr endpointEqual)
  constructor
  · exact
      (drawingCompleteCarrierLink_secondCarrierPort_eq_terminal
        wellFormed degree isLocal linkMember endpointEqual).trans
        (occurrence.targetTerminal_carrierPort_eq_duplicatorArm
          formula aligned)
  · exact
      (drawingCompleteCarrierLink_secondCarrierMacroOrigin_eq_terminal
        wellFormed degree isLocal linkMember endpointEqual).trans
        (occurrence.targetTerminal_scaledDrawingPoint_eq_routedVariableOrigin
          formula wellFormed site occurrenceMember)

/-- If a retained carrier starts at a selected source terminal, its first
boundary interface is exactly the routed-clause fanout interface. -/
theorem drawingCompleteCarrierLink_first_sourceTerminalInterface
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMember :
      link ∈ drawingCompleteCarrierLinks
        (PeriodicCNF.incidenceGraph formula))
    (site : ClauseRouteSite)
    {occurrence : CNFRouteOccurrence Variable}
    (occurrenceMember :
      occurrence ∈ clauseRouteOccurrencesAt formula site)
    (endpointEqual :
      link.first =
        .terminal (occurrence.sourceTerminal formula)) :
    EqualityLink.firstCarrierPort
          (CarrierNode.position
            (PeriodicCNF.incidenceGraph formula)) link =
        (occurrence.sourceTerminal formula).duplicatorArm.carrierPort ∧
      EqualityLink.firstCarrierMacroOrigin
          (CarrierNode.position
            (PeriodicCNF.incidenceGraph formula)) link =
        routedClauseOrigin formula site := by
  have aligned :=
    drawingCompleteCarrierLink_terminal_axisAligned
      wellFormed degree isLocal linkMember (Or.inl endpointEqual)
  constructor
  · exact
      (drawingCompleteCarrierLink_firstCarrierPort_eq_terminal
        wellFormed degree isLocal linkMember endpointEqual).trans
        (occurrence.sourceTerminal_carrierPort_eq_duplicatorArm
          formula aligned)
  · exact
      (drawingCompleteCarrierLink_firstCarrierMacroOrigin_eq_terminal
        wellFormed degree isLocal linkMember endpointEqual).trans
        (occurrence.sourceTerminal_scaledDrawingPoint_eq_routedClauseOrigin
          formula wellFormed site occurrenceMember)

/-- If a retained carrier ends at a selected source terminal, its second
boundary interface is exactly the routed-clause fanout interface. -/
theorem drawingCompleteCarrierLink_second_sourceTerminalInterface
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMember :
      link ∈ drawingCompleteCarrierLinks
        (PeriodicCNF.incidenceGraph formula))
    (site : ClauseRouteSite)
    {occurrence : CNFRouteOccurrence Variable}
    (occurrenceMember :
      occurrence ∈ clauseRouteOccurrencesAt formula site)
    (endpointEqual :
      link.second =
        .terminal (occurrence.sourceTerminal formula)) :
    EqualityLink.secondCarrierPort
          (CarrierNode.position
            (PeriodicCNF.incidenceGraph formula)) link =
        (occurrence.sourceTerminal formula).duplicatorArm.carrierPort ∧
      EqualityLink.secondCarrierMacroOrigin
          (CarrierNode.position
            (PeriodicCNF.incidenceGraph formula)) link =
        routedClauseOrigin formula site := by
  have aligned :=
    drawingCompleteCarrierLink_terminal_axisAligned
      wellFormed degree isLocal linkMember (Or.inr endpointEqual)
  constructor
  · exact
      (drawingCompleteCarrierLink_secondCarrierPort_eq_terminal
        wellFormed degree isLocal linkMember endpointEqual).trans
        (occurrence.sourceTerminal_carrierPort_eq_duplicatorArm
          formula aligned)
  · exact
      (drawingCompleteCarrierLink_secondCarrierMacroOrigin_eq_terminal
        wellFormed degree isLocal linkMember endpointEqual).trans
        (occurrence.sourceTerminal_scaledDrawingPoint_eq_routedClauseOrigin
          formula wellFormed site occurrenceMember)

end PeriodicOrthocrossing
end LeanTrominoes
