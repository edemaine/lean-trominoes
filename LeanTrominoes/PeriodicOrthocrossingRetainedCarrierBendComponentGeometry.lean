import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierPortGeometry

/-!
# Selected retained carrier interfaces at route bends

Either terminal of a certified route-bend corner has the same compass port
and macrocell origin as a selected retained lens incident there.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- A selected retained link beginning at a bend's incoming terminal exposes
the incoming corner interface. -/
theorem retainedDrawingCompleteCarrierLink_first_incomingInterface
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedDrawingCompleteCarrierLinks graph)
    (routeBend : RouteBend)
    (geometry : routeBend.CornerGeometry)
    (endpointEqual :
      link.first = .terminal routeBend.incomingTerminal) :
    EqualityLink.firstCarrierPort
          (CarrierNode.position graph) link =
        routeBend.incomingPort ∧
      EqualityLink.firstCarrierMacroOrigin
          (CarrierNode.position graph) link =
        Cell.scale planarMacroScale
          (routeBend.drawingPoint graph) := by
  constructor
  · exact
      (retainedDrawingCompleteCarrierLink_firstCarrierPort_eq_terminal
        wellFormed degree isLocal linkMem endpointEqual).trans
        (routeBend.incomingTerminal_carrierPort_eq geometry)
  · simpa using
      retainedDrawingCompleteCarrierLink_firstCarrierMacroOrigin_eq_terminal
        wellFormed degree isLocal linkMem endpointEqual

/-- A selected retained link beginning at a bend's outgoing terminal exposes
the outgoing corner interface. -/
theorem retainedDrawingCompleteCarrierLink_first_outgoingInterface
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedDrawingCompleteCarrierLinks graph)
    (routeBend : RouteBend)
    (geometry : routeBend.CornerGeometry)
    (endpointEqual :
      link.first = .terminal routeBend.outgoingTerminal) :
    EqualityLink.firstCarrierPort
          (CarrierNode.position graph) link =
        routeBend.outgoingPort ∧
      EqualityLink.firstCarrierMacroOrigin
          (CarrierNode.position graph) link =
        Cell.scale planarMacroScale
          (routeBend.drawingPoint graph) := by
  constructor
  · exact
      (retainedDrawingCompleteCarrierLink_firstCarrierPort_eq_terminal
        wellFormed degree isLocal linkMem endpointEqual).trans
        (routeBend.outgoingTerminal_carrierPort_eq geometry)
  · simpa using
      retainedDrawingCompleteCarrierLink_firstCarrierMacroOrigin_eq_terminal
        wellFormed degree isLocal linkMem endpointEqual

/-- A selected retained link ending at a bend's incoming terminal exposes
the incoming corner interface. -/
theorem retainedDrawingCompleteCarrierLink_second_incomingInterface
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedDrawingCompleteCarrierLinks graph)
    (routeBend : RouteBend)
    (geometry : routeBend.CornerGeometry)
    (endpointEqual :
      link.second = .terminal routeBend.incomingTerminal) :
    EqualityLink.secondCarrierPort
          (CarrierNode.position graph) link =
        routeBend.incomingPort ∧
      EqualityLink.secondCarrierMacroOrigin
          (CarrierNode.position graph) link =
        Cell.scale planarMacroScale
          (routeBend.drawingPoint graph) := by
  constructor
  · exact
      (retainedDrawingCompleteCarrierLink_secondCarrierPort_eq_terminal
        wellFormed degree isLocal linkMem endpointEqual).trans
        (routeBend.incomingTerminal_carrierPort_eq geometry)
  · simpa using
      retainedDrawingCompleteCarrierLink_secondCarrierMacroOrigin_eq_terminal
        wellFormed degree isLocal linkMem endpointEqual

/-- A selected retained link ending at a bend's outgoing terminal exposes
the outgoing corner interface. -/
theorem retainedDrawingCompleteCarrierLink_second_outgoingInterface
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedDrawingCompleteCarrierLinks graph)
    (routeBend : RouteBend)
    (geometry : routeBend.CornerGeometry)
    (endpointEqual :
      link.second = .terminal routeBend.outgoingTerminal) :
    EqualityLink.secondCarrierPort
          (CarrierNode.position graph) link =
        routeBend.outgoingPort ∧
      EqualityLink.secondCarrierMacroOrigin
          (CarrierNode.position graph) link =
        Cell.scale planarMacroScale
          (routeBend.drawingPoint graph) := by
  constructor
  · exact
      (retainedDrawingCompleteCarrierLink_secondCarrierPort_eq_terminal
        wellFormed degree isLocal linkMem endpointEqual).trans
        (routeBend.outgoingTerminal_carrierPort_eq geometry)
  · simpa using
      retainedDrawingCompleteCarrierLink_secondCarrierMacroOrigin_eq_terminal
        wellFormed degree isLocal linkMem endpointEqual

end PeriodicOrthocrossing
end LeanTrominoes
