/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierPortGeometry

/-!
# Retained carrier interfaces at route bends

Either terminal of a certified route-bend corner has the same compass port
and macrocell origin as a raw retained lens incident there.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- A raw retained link beginning at a bend's incoming terminal exposes
the incoming corner interface. -/
theorem retainedDrawingCompleteCarrierLinkRaw_first_incomingInterface
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedDrawingCompleteCarrierLinksRaw graph)
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
      (retainedDrawingCompleteCarrierLinkRaw_firstCarrierPort_eq_terminal
        wellFormed degree isLocal linkMem endpointEqual).trans
        (routeBend.incomingTerminal_carrierPort_eq geometry)
  · simpa using
      retainedDrawingCompleteCarrierLinkRaw_firstCarrierMacroOrigin_eq_terminal
        wellFormed degree isLocal linkMem endpointEqual

/-- A raw retained link beginning at a bend's outgoing terminal exposes
the outgoing corner interface. -/
theorem retainedDrawingCompleteCarrierLinkRaw_first_outgoingInterface
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedDrawingCompleteCarrierLinksRaw graph)
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
      (retainedDrawingCompleteCarrierLinkRaw_firstCarrierPort_eq_terminal
        wellFormed degree isLocal linkMem endpointEqual).trans
        (routeBend.outgoingTerminal_carrierPort_eq geometry)
  · simpa using
      retainedDrawingCompleteCarrierLinkRaw_firstCarrierMacroOrigin_eq_terminal
        wellFormed degree isLocal linkMem endpointEqual

/-- A raw retained link ending at a bend's incoming terminal exposes
the incoming corner interface. -/
theorem retainedDrawingCompleteCarrierLinkRaw_second_incomingInterface
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedDrawingCompleteCarrierLinksRaw graph)
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
      (retainedDrawingCompleteCarrierLinkRaw_secondCarrierPort_eq_terminal
        wellFormed degree isLocal linkMem endpointEqual).trans
        (routeBend.incomingTerminal_carrierPort_eq geometry)
  · simpa using
      retainedDrawingCompleteCarrierLinkRaw_secondCarrierMacroOrigin_eq_terminal
        wellFormed degree isLocal linkMem endpointEqual

/-- A raw retained link ending at a bend's outgoing terminal exposes
the outgoing corner interface. -/
theorem retainedDrawingCompleteCarrierLinkRaw_second_outgoingInterface
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedDrawingCompleteCarrierLinksRaw graph)
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
      (retainedDrawingCompleteCarrierLinkRaw_secondCarrierPort_eq_terminal
        wellFormed degree isLocal linkMem endpointEqual).trans
        (routeBend.outgoingTerminal_carrierPort_eq geometry)
  · simpa using
      retainedDrawingCompleteCarrierLinkRaw_secondCarrierMacroOrigin_eq_terminal
        wellFormed degree isLocal linkMem endpointEqual

/-! ## Selected-representative compatibility wrappers -/

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
          (routeBend.drawingPoint graph) :=
  retainedDrawingCompleteCarrierLinkRaw_first_incomingInterface
    wellFormed degree isLocal
      ((mem_retainedDrawingCompleteCarrierLinks_iff
        graph link).mp linkMem).1
      routeBend geometry endpointEqual

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
          (routeBend.drawingPoint graph) :=
  retainedDrawingCompleteCarrierLinkRaw_first_outgoingInterface
    wellFormed degree isLocal
      ((mem_retainedDrawingCompleteCarrierLinks_iff
        graph link).mp linkMem).1
      routeBend geometry endpointEqual

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
          (routeBend.drawingPoint graph) :=
  retainedDrawingCompleteCarrierLinkRaw_second_incomingInterface
    wellFormed degree isLocal
      ((mem_retainedDrawingCompleteCarrierLinks_iff
        graph link).mp linkMem).1
      routeBend geometry endpointEqual

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
          (routeBend.drawingPoint graph) :=
  retainedDrawingCompleteCarrierLinkRaw_second_outgoingInterface
    wellFormed degree isLocal
      ((mem_retainedDrawingCompleteCarrierLinks_iff
        graph link).mp linkMem).1
      routeBend geometry endpointEqual

end PeriodicOrthocrossing
end LeanTrominoes
