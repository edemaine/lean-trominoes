/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierCoordinateOrder
import LeanTrominoes.PeriodicOrthocrossingCarrierTerminalPortGeometry

/-!
# Axis interfaces of retained carrier lenses

Every retained link advances in increasing physical carrier order.  Its
first port is therefore east or north and its second port is west or south,
according to the common carrier axis.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- Nodes on one physical carrier have the same axis tag. -/
theorem carrierNode_isHorizontal_iff_of_commonCarrier
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {first second : CarrierNode}
    (firstMem : first ∈ drawingCarrierNodes graph)
    (secondMem : second ∈ drawingCarrierNodes graph)
    (keyEqual : first.carrierKey = second.carrierKey) :
    first.isHorizontal = true ↔
      second.isHorizontal = true := by
  have occurrenceEqual :=
    carrierNode_indexed_translate_eq_of_carrierKey_eq
      graph firstMem secondMem keyEqual
  have firstAligned :
      first.indexed.segment.IsAxisAligned :=
    drawing_isOrthogonal wellFormed isLocal degree
      first.indexed (carrierNode_indexed_mem graph firstMem)
  have secondAligned :
      second.indexed.segment.IsAxisAligned := by
    rw [← occurrenceEqual.1]
    exact firstAligned
  constructor
  · intro firstHorizontalTag
    have firstHorizontal :=
      (carrierNode_isHorizontal_iff
        graph firstMem firstAligned).mp firstHorizontalTag
    have secondHorizontal :
        second.indexed.segment.IsHorizontal := by
      rw [← occurrenceEqual.1]
      exact firstHorizontal
    exact
      (carrierNode_isHorizontal_iff
        graph secondMem secondAligned).mpr secondHorizontal
  · intro secondHorizontalTag
    have secondHorizontal :=
      (carrierNode_isHorizontal_iff
        graph secondMem secondAligned).mp secondHorizontalTag
    have firstHorizontal :
        first.indexed.segment.IsHorizontal := by
      rw [occurrenceEqual.1]
      exact secondHorizontal
    exact
      (carrierNode_isHorizontal_iff
        graph firstMem firstAligned).mpr firstHorizontal

/-- Every retained link advances east or north according to its carrier
axis. -/
theorem drawingCompleteCarrierLink_carrierDirection_eq_axis
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ drawingCompleteCarrierLinks graph) :
    EqualityLink.carrierDirection
        (CarrierNode.position graph) link =
      if link.first.isHorizontal then .east else .north := by
  have clearance :=
    drawingCompleteCarrierLink_hasForwardClearance
      wellFormed degree isLocal linkMem
  by_cases horizontal : link.first.isHorizontal = true
  · rw [if_pos horizontal]
    unfold CarrierNode.HasForwardClearance at clearance
    rw [if_pos horizontal] at clearance
    have xLt :
        (link.first.position graph).1 <
          (link.second.position graph).1 := by
      omega
    simp [EqualityLink.carrierDirection,
      AxisDirection.between, clearance.1, xLt]
  · rw [if_neg horizontal]
    unfold CarrierNode.HasForwardClearance at clearance
    rw [if_neg horizontal] at clearance
    have yLt :
        (link.first.position graph).2 <
          (link.second.position graph).2 := by
      omega
    have yNe :
        (link.first.position graph).2 ≠
          (link.second.position graph).2 :=
      ne_of_lt yLt
    simp [EqualityLink.carrierDirection,
      AxisDirection.between, clearance.1, yLt, yNe]

/-- The first port of a retained link points forward along its carrier. -/
theorem drawingCompleteCarrierLink_firstCarrierPort_eq_axis
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ drawingCompleteCarrierLinks graph) :
    EqualityLink.firstCarrierPort
        (CarrierNode.position graph) link =
      if link.first.isHorizontal then .east else .north := by
  have clearance :=
    drawingCompleteCarrierLink_hasForwardClearance
      wellFormed degree isLocal linkMem
  by_cases horizontal : link.first.isHorizontal = true
  · rw [if_pos horizontal]
    unfold CarrierNode.HasForwardClearance at clearance
    rw [if_pos horizontal] at clearance
    have xLt :
        (link.first.position graph).1 <
          (link.second.position graph).1 := by
      omega
    simp [EqualityLink.firstCarrierPort,
      EqualityLink.carrierDirection,
      AxisDirection.between, clearance.1, xLt,
      AxisDirection.firstCarrierPort]
  · rw [if_neg horizontal]
    unfold CarrierNode.HasForwardClearance at clearance
    rw [if_neg horizontal] at clearance
    have yLt :
        (link.first.position graph).2 <
          (link.second.position graph).2 := by
      omega
    have yNe :
        (link.first.position graph).2 ≠
          (link.second.position graph).2 :=
      ne_of_lt yLt
    simp [EqualityLink.firstCarrierPort,
      EqualityLink.carrierDirection,
      AxisDirection.between, clearance.1, yLt, yNe,
      AxisDirection.firstCarrierPort]

/-- The second port of a retained link points backward along its carrier. -/
theorem drawingCompleteCarrierLink_secondCarrierPort_eq_axis
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ drawingCompleteCarrierLinks graph) :
    EqualityLink.secondCarrierPort
        (CarrierNode.position graph) link =
      if link.first.isHorizontal then .west else .south := by
  have clearance :=
    drawingCompleteCarrierLink_hasForwardClearance
      wellFormed degree isLocal linkMem
  by_cases horizontal : link.first.isHorizontal = true
  · rw [if_pos horizontal]
    unfold CarrierNode.HasForwardClearance at clearance
    rw [if_pos horizontal] at clearance
    have xLt :
        (link.first.position graph).1 <
          (link.second.position graph).1 := by
      omega
    simp [EqualityLink.secondCarrierPort,
      EqualityLink.carrierDirection,
      AxisDirection.between, clearance.1, xLt,
      AxisDirection.secondCarrierPort]
  · rw [if_neg horizontal]
    unfold CarrierNode.HasForwardClearance at clearance
    rw [if_neg horizontal] at clearance
    have yLt :
        (link.first.position graph).2 <
          (link.second.position graph).2 := by
      omega
    have yNe :
        (link.first.position graph).2 ≠
          (link.second.position graph).2 :=
      ne_of_lt yLt
    simp [EqualityLink.secondCarrierPort,
      EqualityLink.carrierDirection,
      AxisDirection.between, clearance.1, yLt, yNe,
      AxisDirection.secondCarrierPort]

end PeriodicOrthocrossing
end LeanTrominoes
