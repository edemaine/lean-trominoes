/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFallbackCardinalForwardOverlapFacts

/-! # Separating a kept forward tangent from the post-lane suffix -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing
open PeriodicOrthocrossing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- At cardinal length at least two, a source gate lies beyond the outer
endpoint of the fixed final radial stub. -/
theorem retainedTerminalFanOuterDemand_cardinal_side_above_finalStub
    (center : Cell)
    (port : Port)
    (length : Nat)
    (slot : RetainedTerminalSlot)
    (cardinal :
      port = .north ∨ port = .east ∨
        port = .south ∨ port = .west)
    (lengthLarge : 2 ≤ length) :
    Cell.linearValue
          (retainedTerminalFanOuterSideNormal (.compass port)) center +
        289 <
      Cell.linearValue
        (retainedTerminalFanOuterSideNormal (.compass port))
        (retainedAngularFanOuterDemand
          center (.compass port, length) slot).gate := by
  rw [retainedAngularFanOuterDemand_gate_eq_interface_ray]
  rcases center with ⟨centerX, centerY⟩
  rcases cardinal with rfl | rfl | rfl | rfl <;>
    simp [retainedTerminalFanOuterSideNormal,
      retainedTerminalInterfaceRadialFactor,
      retainedTerminalFanRefinedInterfaceOffset,
      retainedTerminalInterfaceOffset,
      retainedTerminalInterfaceMultiplier,
      retainedTerminalFanRoutingRefinement,
      RetainedTerminalDirection.primitive,
      Port.unitVector, Cell.linearValue, Cell.add, Cell.scale] <;>
    omega

/-- Every listed point of a cardinal final radial stub is at most one unit
outside its radius-288 lane port. -/
theorem retainedTerminalFanOuterRadialFinalStubAt_cardinal_side_upper
    (center : Cell)
    (port : Port)
    (slot : RetainedTerminalSlot)
    (cardinal :
      port = .north ∨ port = .east ∨
        port = .south ∨ port = .west)
    (point : Cell)
    (pointMember :
      point ∈ retainedTerminalFanOuterRadialFinalStubAt
        center (.compass port) slot) :
    Cell.linearValue
        (retainedTerminalFanOuterSideNormal (.compass port)) point ≤
      Cell.linearValue
          (retainedTerminalFanOuterSideNormal (.compass port)) center +
        289 := by
  unfold retainedTerminalFanOuterRadialFinalStubAt at pointMember
  rw [List.mem_map] at pointMember
  rcases pointMember with ⟨offset, offsetMember, rfl⟩
  rcases center with ⟨centerX, centerY⟩
  rcases cardinal with rfl | rfl | rfl | rfl <;>
    simp [retainedTerminalFanOuterRadialFinalStub,
      compassRay, oppositePort,
      retainedTerminalFanOuterLanePortOffset,
      retainedTerminalFanRefinedInterfaceOffset,
      retainedTerminalInterfaceOffset,
      retainedTerminalInterfaceMultiplier,
      retainedTerminalFanRoutingRefinement,
      retainedTerminalFanOuterLaneOffset,
      retainedTerminalFanOuterLaneStep,
      retainedTerminalFanOuterLaneSpacing,
      retainedTerminalFanOuterSideNormal,
      RetainedTerminalDirection.primitive,
      Port.unitVector, Cell.linearValue, Cell.add, Cell.scale]
      at offsetMember ⊢ <;>
    rcases offsetMember with rfl | rfl <;> simp

/-- A cardinal final radial stub is continuously separated from a forward
source tangent at every terminal of length at least two. -/
theorem retainedTerminalFanOuterRadialFinalStubAt_strictlyAvoids_cardinalForwardTangent
    (center : Cell)
    (port : Port)
    (length : Nat)
    (slot : RetainedTerminalSlot)
    (distance : Nat)
    (cardinal :
      port = .north ∨ port = .east ∨
        port = .south ∨ port = .west)
    (lengthLarge : 2 ≤ length) :
    RoutesStrictlyAvoidEachOther
      (retainedTerminalFanOuterRadialFinalStubAt
        center (.compass port) slot)
      (retainedTerminalFanCardinalForwardTangentRoute
        center port length slot distance) := by
  apply routesStrictlyAvoidEachOther_of_linear_separated
    (retainedTerminalFanOuterSideNormal (.compass port))
    (Cell.linearValue
        (retainedTerminalFanOuterSideNormal (.compass port)) center +
      289)
  · exact retainedTerminalFanOuterRadialFinalStubAt_cardinal_side_upper
      center port slot cardinal
  · intro point pointMember
    rw [retainedTerminalFanCardinalForwardTangentRoute_side_value
      center port length slot distance cardinal point pointMember]
    exact retainedTerminalFanOuterDemand_cardinal_side_above_finalStub
      center port length slot cardinal lengthLarge

/-- The complete fixed terminal tail—final radial stub, local adapter, and
Figure 7 spoke—is separated from a cardinal forward tangent. -/
theorem retainedFallbackFanTerminalTailRouteAt_strictlyAvoids_cardinalForwardTangent
    (center : Cell)
    (port : Port)
    (length : Nat)
    (slot : RetainedTerminalSlot)
    (distance : Nat)
    (cardinal :
      port = .north ∨ port = .east ∨
        port = .south ∨ port = .west)
    (lengthLarge : 2 ≤ length) :
    RoutesStrictlyAvoidEachOther
      (retainedFallbackFanTerminalTailRouteAt
        center (.compass port) slot)
      (retainedTerminalFanCardinalForwardTangentRoute
        center port length slot distance) := by
  let stub := retainedTerminalFanOuterRadialFinalStubAt
    center (.compass port) slot
  let localRoute := retainedTerminalFanOuterLocalRouteAt
    center (.compass port) slot
  let spoke := retainedTerminalFanFigure7SpokeRouteAt center slot
  let finiteTail := retainedFallbackFanFiniteTailRouteAt
    center (.compass port) slot
  let tangent := retainedTerminalFanCardinalForwardTangentRoute
    center port length slot distance
  have stubAvoid : RoutesStrictlyAvoidEachOther stub tangent :=
    retainedTerminalFanOuterRadialFinalStubAt_strictlyAvoids_cardinalForwardTangent
      center port length slot distance cardinal lengthLarge
  have localAvoid : RoutesStrictlyAvoidEachOther localRoute tangent :=
    retainedTerminalFanOuterLocalRouteAt_strictlyAvoids_cardinalForwardTangent
      center port length slot distance cardinal lengthLarge
  have spokeAvoid : RoutesStrictlyAvoidEachOther spoke tangent :=
    retainedTerminalFanFigure7SpokeRouteAt_strictlyAvoids_cardinalForwardTangent
      center port length slot distance cardinal lengthLarge
  have localLast := retainedTerminalFanOuterLocalRouteAt_getLast?
    center (.compass port) slot
  have spokeHead := retainedTerminalFanFigure7SpokeRouteAt_head?
    center slot
  have finiteAvoid : RoutesStrictlyAvoidEachOther finiteTail tangent := by
    change RoutesStrictlyAvoidEachOther
      (joinAtEndpoint localRoute spoke) tangent
    exact localAvoid.join_left spokeAvoid localLast spokeHead
  have stubLast := retainedTerminalFanOuterRadialFinalStubAt_getLast?
    center (.compass port) slot
  have finiteHead : finiteTail.head? =
      some (retainedTerminalFanOuterLanePort
        center (.compass port) slot) := by
    change (joinAtEndpoint localRoute spoke).head? = _
    exact joinAtEndpoint_head?
      (retainedTerminalFanOuterLocalRouteAt_head?
        center (.compass port) slot)
  change RoutesStrictlyAvoidEachOther
    (joinAtEndpoint stub finiteTail) tangent
  exact stubAvoid.join_left finiteAvoid stubLast finiteHead

/-- After its shifted-gate head, the shortened cardinal inward ray lies
strictly inside the forward tangent's supporting side. -/
theorem retainedTerminalFanOuterInwardPrefixRay_unit_tail_cardinal_side_lt_start
    (port : Port)
    (length : Nat)
    (start point : Cell)
    (cardinal :
      port = .north ∨ port = .east ∨
        port = .south ∨ port = .west)
    (lengthLarge : 2 ≤ length)
    (pointMember :
      point ∈
        (AxisDirection.unitSubdividePolyline
          ((retainedTerminalFanOuterInwardPrefixRay
            (.compass port, length)).rasterize start)).tail) :
    Cell.linearValue
        (retainedTerminalFanOuterSideNormal (.compass port)) point <
      Cell.linearValue
        (retainedTerminalFanOuterSideNormal (.compass port)) start := by
  let terminal : RetainedTerminalData := (.compass port, length)
  have countPositive :
      0 < retainedTerminalFanOuterRadialLength terminal - 1 := by
    rcases cardinal with rfl | rfl | rfl | rfl <;>
      simp [terminal, retainedTerminalFanOuterRadialLength,
        retainedTerminalFanTotalRefinement,
        PeriodicEightOccurrenceSplitPositioned.refinementScale,
        retainedTerminalFanRoutingRefinement,
        retainedTerminalInterfaceMultiplier] at lengthLarge ⊢ <;>
      omega
  have pointMember' :
      point ∈
        (AxisDirection.unitSubdividePolyline
          ((retainedTerminalFanOuterInwardRayOfLength
            terminal.1
            (retainedTerminalFanOuterRadialLength terminal - 1)).rasterize
              start)).tail := by
    simpa [terminal,
      FallbackSuffixDirectionCompiler.retainedTerminalFanOuterInwardPrefixRay_eq_ofLength]
      using pointMember
  have progressed :=
    FallbackSuffixDirectionCompiler.retainedTerminalFanOuterInwardRayOfLength_tail_join_gt_start
      terminal.1
      (retainedTerminalFanOuterRadialLength terminal - 1)
      start point countPositive pointMember'
  have normalEq :
      FallbackSuffixDirectionCompiler.retainedFallbackRadialJoinNormal
          terminal.1 =
        Cell.scale (-1)
          (retainedTerminalFanOuterSideNormal terminal.1) := by
    dsimp [terminal]
    rcases cardinal with rfl | rfl | rfl | rfl <;> native_decide
  rw [normalEq] at progressed
  rcases start with ⟨startX, startY⟩
  rcases point with ⟨pointX, pointY⟩
  simp [terminal, Cell.linearValue, Cell.scale] at progressed ⊢
  omega

/-- Every subdivided point of the kept part of a cardinal forward tangent
has the source gate's exact supporting-side value. -/
theorem retainedTerminalFanCardinalForwardTangentLeadingRoute_unit_side_value
    (center : Cell)
    (port : Port)
    (length : Nat)
    (slot : RetainedTerminalSlot)
    (distance : Nat)
    (cardinal :
      port = .north ∨ port = .east ∨
        port = .south ∨ port = .west)
    (point : Cell)
    (pointMember :
      point ∈ AxisDirection.unitSubdividePolyline
        (retainedTerminalFanCardinalForwardTangentLeadingRoute
          center port length slot distance)) :
    Cell.linearValue
        (retainedTerminalFanOuterSideNormal (.compass port)) point =
      Cell.linearValue
        (retainedTerminalFanOuterSideNormal (.compass port))
        (retainedAngularFanOuterDemand
          center (.compass port, length) slot).gate := by
  let gate :=
    (retainedAngularFanOuterDemand
      center (.compass port, length) slot).gate
  let source := Cell.add gate
    (Cell.scale distance
      (retainedTerminalFanOuterLaneStep (.compass port)))
  let shiftedGate := Cell.add gate
    (retainedTerminalFanOuterLaneOffset (.compass port) slot)
  change Cell.linearValue
      (retainedTerminalFanOuterSideNormal (.compass port)) point =
    Cell.linearValue
      (retainedTerminalFanOuterSideNormal (.compass port)) gate
  change point ∈ AxisDirection.unitSubdividePolyline
    [source, shiftedGate] at pointMember
  simp only [AxisDirection.unitSubdividePolyline,
    joinAtEndpoint, List.tail_cons, List.append_nil] at pointMember
  unfold AxisDirection.unitSegmentPoints at pointMember
  rw [List.mem_map] at pointMember
  rcases pointMember with ⟨index, indexMember, rfl⟩
  rcases gate with ⟨gateX, gateY⟩
  rcases cardinal with rfl | rfl | rfl | rfl <;>
    simp [source, shiftedGate,
      retainedTerminalFanOuterSideNormal,
      retainedTerminalFanOuterLaneStep,
      retainedTerminalFanOuterLaneOffset,
      retainedTerminalFanOuterLaneSpacing,
      AxisDirection.between, AxisDirection.step,
      Cell.linearValue, Cell.add, Cell.scale] <;>
    split_ifs <;> simp_all

/-- The kept forward-tangent unit path is disjoint from every normalized
ordinary-suffix point strictly after the shifted gate. -/
theorem retainedTerminalFanCardinalForwardTangentLeadingRoute_unit_disjoint_afterLaneRest
    (center : Cell)
    (port : Port)
    (length : Nat)
    (slot : RetainedTerminalSlot)
    (distance : Nat)
    (cardinal :
      port = .north ∨ port = .east ∨
        port = .south ∨ port = .west)
    (lengthLarge : 2 ≤ length)
    (shiftStrict :
      retainedTerminalFanOuterLaneSpacing * slot.val < distance) :
    List.Disjoint
      (AxisDirection.unitSubdividePolyline
        (retainedTerminalFanCardinalForwardTangentLeadingRoute
          center port length slot distance))
      (retainedTerminalFanCardinalOrdinaryAfterLaneRest
        center port length slot) := by
  let terminal : RetainedTerminalData := (.compass port, length)
  let gate := (retainedAngularFanOuterDemand center terminal slot).gate
  let shiftedGate := Cell.add gate
    (retainedTerminalFanOuterLaneOffset terminal.1 slot)
  let tangent := retainedTerminalFanCardinalForwardTangentRoute
    center port length slot distance
  let tangentLeading :=
    retainedTerminalFanCardinalForwardTangentLeadingRoute
      center port length slot distance
  let overlapRoute :=
    retainedTerminalFanCardinalForwardTangentOverlapRoute
      center port length slot
  let splitTangent :=
    retainedTerminalFanCardinalForwardTangentSplitRoute
      center port length slot distance
  let inwardRoute :=
    (retainedTerminalFanOuterInwardPrefixRay terminal).rasterize
      shiftedGate
  let terminalTail := retainedFallbackFanTerminalTailRouteAt
    center terminal.1 slot
  let normalizedTail :=
    AxisDirection.normalizeOrthogonalPolyline terminalTail
  let rest := retainedTerminalFanCardinalOrdinaryAfterLaneRest
    center port length slot
  have distancePositive : 0 < distance := by omega
  have tangentOrthogonal : OrthogonalPolyline tangent :=
    retainedTerminalFanCardinalForwardTangentRoute_orthogonal
      center port length slot distance cardinal distancePositive
  have tangentLeadingNonempty : tangentLeading ≠ [] := by
    simp [tangentLeading,
      retainedTerminalFanCardinalForwardTangentLeadingRoute]
  have tangentLeadingLast : tangentLeading.getLast? =
      some shiftedGate := by
    simp [tangentLeading, shiftedGate, gate, terminal]
  have overlapHead : overlapRoute.head? = some shiftedGate := by
    simp [overlapRoute, shiftedGate, gate, terminal]
  have splitSubdivision :
      AxisDirection.unitSubdividePolyline splitTangent =
        joinAtEndpoint
          (AxisDirection.unitSubdividePolyline tangentLeading)
          (AxisDirection.unitSubdividePolyline overlapRoute) := by
    change AxisDirection.unitSubdividePolyline
        (joinAtEndpoint tangentLeading overlapRoute) = _
    exact AxisDirection.unitSubdividePolyline_joinAtEndpoint
      tangentLeadingNonempty tangentLeadingLast overlapHead
  have tangentSubdivision :
      AxisDirection.unitSubdividePolyline tangent =
        AxisDirection.unitSubdividePolyline splitTangent :=
    retainedTerminalFanCardinalForwardTangentRoute_unitSubdivide_eq_split
      center port length slot distance cardinal shiftStrict
  have tangentLeadingMemTangent :
      ∀ point,
        point ∈ AxisDirection.unitSubdividePolyline tangentLeading →
        point ∈ AxisDirection.unitSubdividePolyline tangent := by
    intro point pointMember
    rw [tangentSubdivision, splitSubdivision]
    unfold joinAtEndpoint
    exact List.mem_append_left _ pointMember
  have terminalTailNonempty : terminalTail ≠ [] :=
    retainedFallbackFanTerminalTailRouteAt_ne_nil
      center terminal.1 slot
  have terminalTailOrthogonal : OrthogonalPolyline terminalTail :=
    retainedFallbackFanTerminalTailRouteAt_orthogonal
      center terminal.1 slot
  have tangentTerminalDisjoint :
      List.Disjoint
        (AxisDirection.unitSubdividePolyline tangent)
        (AxisDirection.unitSubdividePolyline terminalTail) :=
    (retainedFallbackFanTerminalTailRouteAt_strictlyAvoids_cardinalForwardTangent
      center port length slot distance cardinal lengthLarge).symm
      |>.unitSubdividePolyline_disjoint
        tangentOrthogonal terminalTailOrthogonal
  have normalizedTailSublist :
      normalizedTail.Sublist
        (AxisDirection.unitSubdividePolyline terminalTail) :=
    AxisDirection.normalizeOrthogonalPolyline_sublist_unitSubdividePolyline
      terminalTailNonempty terminalTailOrthogonal
  have restEq :
      rest =
        (AxisDirection.unitSubdividePolyline inwardRoute).tail ++
          normalizedTail.tail := by
    rfl
  have shiftedSide :
      Cell.linearValue
          (retainedTerminalFanOuterSideNormal terminal.1) shiftedGate =
        Cell.linearValue
          (retainedTerminalFanOuterSideNormal terminal.1) gate := by
    rcases cardinal with rfl | rfl | rfl | rfl <;>
      simp [terminal, shiftedGate,
        retainedTerminalFanOuterSideNormal,
        retainedTerminalFanOuterLaneOffset,
        retainedTerminalFanOuterLaneStep,
        retainedTerminalFanOuterLaneSpacing,
        Cell.linearValue, Cell.add, Cell.scale]
  intro point tangentLeadingMember restMember
  change point ∈ rest at restMember
  rw [restEq, List.mem_append] at restMember
  rcases restMember with inwardMember | normalizedTailMember
  · have tangentSide :=
      retainedTerminalFanCardinalForwardTangentLeadingRoute_unit_side_value
        center port length slot distance cardinal point
        tangentLeadingMember
    have inwardSide :=
      retainedTerminalFanOuterInwardPrefixRay_unit_tail_cardinal_side_lt_start
        port length shiftedGate point cardinal lengthLarge inwardMember
    change Cell.linearValue
        (retainedTerminalFanOuterSideNormal terminal.1) point =
      Cell.linearValue
        (retainedTerminalFanOuterSideNormal terminal.1) gate
      at tangentSide
    dsimp [terminal] at tangentSide inwardSide shiftedSide
    rw [shiftedSide] at inwardSide
    omega
  · have normalizedTailMember' : point ∈ normalizedTail :=
      List.mem_of_mem_tail normalizedTailMember
    have terminalTailMember :
        point ∈ AxisDirection.unitSubdividePolyline terminalTail :=
      normalizedTailSublist.subset normalizedTailMember'
    exact tangentTerminalDisjoint
      (tangentLeadingMemTangent point tangentLeadingMember)
      terminalTailMember

end PeriodicEightOccurrenceSplit
end LeanTrominoes
