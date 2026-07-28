import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierPortGeometry
import LeanTrominoes.PeriodicOrthocrossingCarrierTerminalComponentGeometry

/-!
# Selected retained carrier interfaces at routed terminals

For selected route occurrences, the exact terminal port and macrocell origin
of a retained carrier lens agree with the corresponding routed-variable or
routed-clause component interface.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 800000

/-- A selected retained carrier beginning at a target terminal exposes the
routed-variable arm interface. -/
theorem retainedDrawingCompleteCarrierLink_first_targetTerminalInterface
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
      link ∈ retainedDrawingCompleteCarrierLinks
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
    retainedDrawingCompleteCarrierLink_terminal_axisAligned
      wellFormed degree isLocal linkMember (Or.inl endpointEqual)
  constructor
  · exact
      (retainedDrawingCompleteCarrierLink_firstCarrierPort_eq_terminal
        wellFormed degree isLocal linkMember endpointEqual).trans
        (occurrence.targetTerminal_carrierPort_eq_duplicatorArm
          formula aligned)
  · exact
      (retainedDrawingCompleteCarrierLink_firstCarrierMacroOrigin_eq_terminal
        wellFormed degree isLocal linkMember endpointEqual).trans
        (occurrence.targetTerminal_scaledDrawingPoint_eq_routedVariableOrigin
          formula wellFormed site occurrenceMember)

/-- A selected retained carrier ending at a target terminal exposes the
routed-variable arm interface. -/
theorem retainedDrawingCompleteCarrierLink_second_targetTerminalInterface
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
      link ∈ retainedDrawingCompleteCarrierLinks
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
    retainedDrawingCompleteCarrierLink_terminal_axisAligned
      wellFormed degree isLocal linkMember (Or.inr endpointEqual)
  constructor
  · exact
      (retainedDrawingCompleteCarrierLink_secondCarrierPort_eq_terminal
        wellFormed degree isLocal linkMember endpointEqual).trans
        (occurrence.targetTerminal_carrierPort_eq_duplicatorArm
          formula aligned)
  · exact
      (retainedDrawingCompleteCarrierLink_secondCarrierMacroOrigin_eq_terminal
        wellFormed degree isLocal linkMember endpointEqual).trans
        (occurrence.targetTerminal_scaledDrawingPoint_eq_routedVariableOrigin
          formula wellFormed site occurrenceMember)

/-- A selected retained carrier beginning at a source terminal exposes the
routed-clause fanout interface. -/
theorem retainedDrawingCompleteCarrierLink_first_sourceTerminalInterface
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
      link ∈ retainedDrawingCompleteCarrierLinks
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
    retainedDrawingCompleteCarrierLink_terminal_axisAligned
      wellFormed degree isLocal linkMember (Or.inl endpointEqual)
  constructor
  · exact
      (retainedDrawingCompleteCarrierLink_firstCarrierPort_eq_terminal
        wellFormed degree isLocal linkMember endpointEqual).trans
        (occurrence.sourceTerminal_carrierPort_eq_duplicatorArm
          formula aligned)
  · exact
      (retainedDrawingCompleteCarrierLink_firstCarrierMacroOrigin_eq_terminal
        wellFormed degree isLocal linkMember endpointEqual).trans
        (occurrence.sourceTerminal_scaledDrawingPoint_eq_routedClauseOrigin
          formula wellFormed site occurrenceMember)

/-- A selected retained carrier ending at a source terminal exposes the
routed-clause fanout interface. -/
theorem retainedDrawingCompleteCarrierLink_second_sourceTerminalInterface
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
      link ∈ retainedDrawingCompleteCarrierLinks
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
    retainedDrawingCompleteCarrierLink_terminal_axisAligned
      wellFormed degree isLocal linkMember (Or.inr endpointEqual)
  constructor
  · exact
      (retainedDrawingCompleteCarrierLink_secondCarrierPort_eq_terminal
        wellFormed degree isLocal linkMember endpointEqual).trans
        (occurrence.sourceTerminal_carrierPort_eq_duplicatorArm
          formula aligned)
  · exact
      (retainedDrawingCompleteCarrierLink_secondCarrierMacroOrigin_eq_terminal
        wellFormed degree isLocal linkMember endpointEqual).trans
        (occurrence.sourceTerminal_scaledDrawingPoint_eq_routedClauseOrigin
          formula wellFormed site occurrenceMember)

end PeriodicOrthocrossing
end LeanTrominoes
