import LeanTrominoes.OrthogonalPolylineMiddleCoarsening
import LeanTrominoes.RetainedAngularFanOuterZeroRadialRoutes

/-!
# Decomposing positive outer radial fan routes

To splice the exterior radial lanes into the finite fan, we isolate the
last primitive block of every positive radial route.  Diagonal compass rays
and routed-clause rays already expose that block as a separate orthogonal
polyline.  A cardinal compass ray represents the same geometry by one long
segment, so its split form must instead be coarsened after separation has
been proved.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Peel the final primitive block from a repeated diagonal staircase. -/
theorem diagonalStaircase_split_last
    (horizontal vertical : Int)
    (length : Nat) (start : Cell) :
    diagonalStaircase horizontal vertical (length + 1) start =
      joinAtEndpoint
        (diagonalStaircase horizontal vertical length start)
        (diagonalStaircase horizontal vertical 1
          (Cell.add start
            (Cell.scale length (horizontal, vertical)))) := by
  induction length generalizing start with
  | zero =>
      simp [diagonalStaircase, joinAtEndpoint, Cell.add, Cell.scale]
  | succ length induction =>
      change
        start ::
            Cell.add start (horizontal, 0) ::
              diagonalStaircase horizontal vertical (length + 1)
                (Cell.add start (horizontal, vertical)) =
          joinAtEndpoint
            (start ::
              Cell.add start (horizontal, 0) ::
                diagonalStaircase horizontal vertical length
                  (Cell.add start (horizontal, vertical)))
            (diagonalStaircase horizontal vertical 1
              (Cell.add start
                (Cell.scale (length + 1)
                  (horizontal, vertical))))
      rw [joinAtEndpoint]
      simp only [List.cons_append]
      rw [induction]
      rw [joinAtEndpoint]
      have startEq :
          Cell.add
              (Cell.add start (horizontal, vertical))
              (Cell.scale length (horizontal, vertical)) =
            Cell.add start
              (Cell.scale (length + 1)
                (horizontal, vertical)) := by
        apply Prod.ext <;>
          simp [Cell.add, Cell.scale] <;>
          ring
      rw [startEq]

@[simp]
theorem compassRay_southeast_eq_diagonalStaircase
    (length : Nat) (start : Cell) :
    compassRay .southeast length start =
      diagonalStaircase 1 1 length start := by
  cases length <;> rfl

@[simp]
theorem compassRay_northwest_eq_diagonalStaircase
    (length : Nat) (start : Cell) :
    compassRay .northwest length start =
      diagonalStaircase (-1) (-1) length start := by
  cases length <;> rfl

@[simp]
theorem compassRay_northeast_eq_diagonalStaircase
    (length : Nat) (start : Cell) :
    compassRay .northeast length start =
      diagonalStaircase 1 (-1) length start := by
  cases length <;> rfl

@[simp]
theorem compassRay_southwest_eq_diagonalStaircase
    (length : Nat) (start : Cell) :
    compassRay .southwest length start =
      diagonalStaircase (-1) 1 length start := by
  cases length <;> rfl

/-- Peel the final exceptional primitive block from a routed-clause ray. -/
theorem routedClauseRay_split_last
    (arm : PlanarThreeSAT.DuplicatorArm)
    (length : Nat) (start : Cell) :
    routedClauseRay arm (length + 1) start =
      joinAtEndpoint
        (routedClauseRay arm length start)
        (routedClauseRay arm 1
          (Cell.add start
            (Cell.scale length
              (routedClauseRayPrimitive arm)))) := by
  induction length generalizing start with
  | zero =>
      rw [routedClauseRay, routedClauseRay]
      simp only [joinAtEndpoint]
      generalize blockEq :
          routedClauseRayBlock arm start = block
      cases block with
      | nil =>
          have head :=
            routedClauseRayBlock_head? arm start
          simp [blockEq] at head
      | cons head tail =>
          have headEq : head = start := by
            have headLookup :=
              routedClauseRayBlock_head? arm start
            simpa [blockEq] using headLookup
          subst head
          simp [routedClauseRay, joinAtEndpoint,
            blockEq, Cell.add, Cell.scale]
  | succ length induction =>
      change
        joinAtEndpoint
            (routedClauseRayBlock arm start)
            (routedClauseRay arm (length + 1)
              (Cell.add start
                (routedClauseRayPrimitive arm))) =
          joinAtEndpoint
            (joinAtEndpoint
              (routedClauseRayBlock arm start)
              (routedClauseRay arm length
                (Cell.add start
                  (routedClauseRayPrimitive arm))))
            (routedClauseRay arm 1
              (Cell.add start
                (Cell.scale (length + 1)
                  (routedClauseRayPrimitive arm))))
      rw [induction]
      have startEq :
          Cell.add
              (Cell.add start
                (routedClauseRayPrimitive arm))
              (Cell.scale length
                (routedClauseRayPrimitive arm)) =
            Cell.add start
              (Cell.scale (length + 1)
                (routedClauseRayPrimitive arm)) := by
        apply Prod.ext <;>
          simp [Cell.add, Cell.scale] <;>
          ring
      rw [startEq]
      have rayNe :
          routedClauseRay arm length
              (Cell.add start
                (routedClauseRayPrimitive arm)) ≠ [] := by
        intro empty
        have head :=
          routedClauseRay_head? arm length
            (Cell.add start
              (routedClauseRayPrimitive arm))
        simp [empty] at head
      unfold joinAtEndpoint
      rw [List.tail_append_of_ne_nil rayNe]
      exact (List.append_assoc _ _ _).symm

/-- Whether the compass raster uses intermediate elbow vertices in every
primitive block. -/
def portUsesDiagonalRaster :
    OccurrenceSplitRing.Port → Prop
  | .northwest | .northeast | .southeast | .southwest => True
  | .north | .east | .south | .west => False

/-- Peel the last primitive block from any diagonal compass ray. -/
theorem compassRay_split_last_of_usesDiagonalRaster
    (port : OccurrenceSplitRing.Port)
    (length : Nat) (start : Cell)
    (diagonal : portUsesDiagonalRaster port) :
    compassRay port (length + 1) start =
      joinAtEndpoint
        (compassRay port length start)
        (compassRay port 1
          (Cell.add start
            (Cell.scale length port.unitVector))) := by
  cases port <;>
    simp [portUsesDiagonalRaster]
      at diagonal ⊢ <;>
    exact diagonalStaircase_split_last _ _ length start

/-- A raster is blocked when every primitive step is represented by a
nontrivial polyline block instead of being merged into one cardinal
segment. -/
def RetainedTerminalDirection.usesBlockedRaster :
    RetainedTerminalDirection → Prop
  | .compass port => portUsesDiagonalRaster port
  | .routedClause _ => True

/-- A positive radial route with its last primitive block explicitly
separated from its prefix. -/
def splitRadialRoute
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot) : List Cell :=
  joinAtEndpoint
    (retainedTerminalFanOuterRadialPrefix center terminal slot)
    (retainedTerminalFanOuterRadialFinalStubAt
      center terminal.1 slot)

/-- The finite final stub is exactly a one-step inward compass ray. -/
theorem retainedTerminalFanOuterRadialFinalStubAt_compass
    (center : Cell)
    (port : OccurrenceSplitRing.Port)
    (slot : RetainedTerminalSlot) :
    retainedTerminalFanOuterRadialFinalStubAt
        center (.compass port) slot =
      compassRay (oppositePort port) 1
        (Cell.add center
          (Cell.add
            (retainedTerminalFanOuterLanePortOffset
              (.compass port) slot)
            (RetainedTerminalDirection.compass port).primitive)) := by
  cases port <;>
    simp [
      retainedTerminalFanOuterRadialFinalStubAt,
      retainedTerminalFanOuterRadialFinalStub,
      oppositePort, compassRay, diagonalStaircase,
      RetainedTerminalDirection.primitive,
      OccurrenceSplitRing.Port.unitVector,
      Cell.add, Cell.scale] <;>
    try {constructor <;> ring} <;>
    ring

/-- The finite final stub is exactly one routed-clause primitive block. -/
theorem retainedTerminalFanOuterRadialFinalStubAt_routedClause
    (center : Cell)
    (arm : PlanarThreeSAT.DuplicatorArm)
    (slot : RetainedTerminalSlot) :
    retainedTerminalFanOuterRadialFinalStubAt
        center (.routedClause arm) slot =
      routedClauseRay arm 1
        (Cell.add center
          (Cell.add
            (retainedTerminalFanOuterLanePortOffset
              (.routedClause arm) slot)
            (RetainedTerminalDirection.routedClause arm).primitive)) := by
  cases arm <;>
    simp [
      retainedTerminalFanOuterRadialFinalStubAt,
      retainedTerminalFanOuterRadialFinalStub,
      routedClauseRay, routedClauseRayBlock,
      routedClauseRayOffsets,
      routedClauseRayPrimitive,
      RetainedTerminalDirection.primitive,
      joinAtEndpoint, Cell.add, Cell.sub] <;>
    repeat
      first | constructor | ring

/-- For blocked rasters, explicitly splitting the final primitive block
does not change the represented route. -/
theorem radialRoute_eq_split_of_usesBlockedRaster
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (radialPositive :
      0 < retainedTerminalFanOuterRadialLength terminal)
    (blocked : terminal.1.usesBlockedRaster) :
    retainedTerminalFanOuterRadialRoute center terminal slot =
      splitRadialRoute center terminal slot := by
  rcases terminal with ⟨direction, length⟩
  cases direction with
  | compass port =>
      have inwardDiagonal :
          portUsesDiagonalRaster (oppositePort port) := by
        cases port <;>
          simp [
            RetainedTerminalDirection.usesBlockedRaster,
            portUsesDiagonalRaster,
            oppositePort] at blocked ⊢
      generalize radialEq :
          retainedTerminalFanOuterRadialLength
            (.compass port, length) = radialLength
          at radialPositive ⊢
      cases radialLength with
      | zero => omega
      | succ radialLength =>
          rw [retainedTerminalFanOuterRadialRoute,
            splitRadialRoute,
            retainedTerminalFanOuterRadialPrefix]
          simp only [
            retainedTerminalFanOuterInwardRay,
            retainedTerminalFanOuterInwardPrefixRay,
            RetainedRay.rasterize]
          rw [radialEq]
          simp only [Nat.add_sub_cancel]
          rw [compassRay_split_last_of_usesDiagonalRaster
            (oppositePort port) radialLength _ inwardDiagonal]
          have prefixNe :
              compassRay (oppositePort port) radialLength
                  (Cell.add
                    (retainedAngularFanOuterDemand center
                      (.compass port, length) slot).gate
                    (retainedTerminalFanOuterLaneOffset
                      (.compass port) slot)) ≠ [] := by
            intro empty
            have head :=
              compassRay_head? (oppositePort port) radialLength
                (Cell.add
                  (retainedAngularFanOuterDemand center
                    (.compass port, length) slot).gate
                  (retainedTerminalFanOuterLaneOffset
                    (.compass port) slot))
            simp [empty] at head
          rw [joinAtEndpoint_assoc_of_middle_ne_nil prefixNe]
          apply congrArg (joinAtEndpoint _)
          have finishEq :=
            retainedTerminalFanOuterInwardPrefix_finish_eq
              center (.compass port, length) slot
              (by rw [radialEq]; omega)
          simp [
            retainedTerminalFanOuterInwardPrefixRay,
            RetainedRay.vector, radialEq]
            at finishEq
          rw [finishEq]
          exact
            (retainedTerminalFanOuterRadialFinalStubAt_compass
              center port slot).symm
  | routedClause arm =>
      generalize radialEq :
          retainedTerminalFanOuterRadialLength
            (.routedClause arm, length) = radialLength
          at radialPositive ⊢
      cases radialLength with
      | zero => omega
      | succ radialLength =>
          rw [retainedTerminalFanOuterRadialRoute,
            splitRadialRoute,
            retainedTerminalFanOuterRadialPrefix]
          simp only [
            retainedTerminalFanOuterInwardRay,
            retainedTerminalFanOuterInwardPrefixRay,
            RetainedRay.rasterize]
          rw [radialEq]
          simp only [Nat.add_sub_cancel]
          rw [routedClauseRay_split_last]
          have prefixNe :
              routedClauseRay arm radialLength
                  (Cell.add
                    (retainedAngularFanOuterDemand center
                      (.routedClause arm, length) slot).gate
                    (retainedTerminalFanOuterLaneOffset
                      (.routedClause arm) slot)) ≠ [] := by
            intro empty
            have head :=
              routedClauseRay_head? arm radialLength
                (Cell.add
                  (retainedAngularFanOuterDemand center
                    (.routedClause arm, length) slot).gate
                  (retainedTerminalFanOuterLaneOffset
                    (.routedClause arm) slot))
            simp [empty] at head
          rw [joinAtEndpoint_assoc_of_middle_ne_nil prefixNe]
          apply congrArg (joinAtEndpoint _)
          have finishEq :=
            retainedTerminalFanOuterInwardPrefix_finish_eq
              center (.routedClause arm, length) slot
              (by rw [radialEq]; omega)
          simp [
            retainedTerminalFanOuterInwardPrefixRay,
            RetainedRay.vector, radialEq]
            at finishEq
          rw [finishEq]
          exact
            (retainedTerminalFanOuterRadialFinalStubAt_routedClause
              center arm slot).symm

/-- The explicitly split earlier radial route avoids a later local route. -/
theorem splitRadialRoute_strictlyAvoid_laterLocal
    (center : Cell)
    (firstTerminal : RetainedTerminalData)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (secondDirection : RetainedTerminalDirection)
    (radialPositive :
      0 < retainedTerminalFanOuterRadialLength firstTerminal)
    (directionsLe :
      firstTerminal.1.angularRank ≤ secondDirection.angularRank)
    (slotsLt : firstSlot.val < secondSlot.val) :
    RoutesStrictlyAvoidEachOther
      (splitRadialRoute center firstTerminal firstSlot)
      (retainedTerminalFanOuterLocalRouteAt
        center secondDirection secondSlot) := by
  unfold splitRadialRoute
  exact
    (retainedTerminalFanOuterRadialPrefix_strictlyAvoid_local
      center firstTerminal firstSlot secondSlot secondDirection
      radialPositive).join_left
      (retainedTerminalFanOuterRadialFinalStubAt_strictlyAvoid_laterLocal
        center firstTerminal.1 secondDirection
        firstSlot secondSlot directionsLe slotsLt)
      (retainedTerminalFanOuterRadialPrefix_getLast?
        center firstTerminal firstSlot radialPositive)
      (retainedTerminalFanOuterRadialFinalStubAt_head?
        center firstTerminal.1 firstSlot)

/-- An earlier local route avoids the explicitly split later radial route. -/
theorem local_strictlyAvoid_laterSplitRadialRoute
    (center : Cell)
    (firstDirection : RetainedTerminalDirection)
    (secondTerminal : RetainedTerminalData)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (radialPositive :
      0 < retainedTerminalFanOuterRadialLength secondTerminal)
    (directionsLe :
      firstDirection.angularRank ≤ secondTerminal.1.angularRank)
    (slotsLt : firstSlot.val < secondSlot.val) :
    RoutesStrictlyAvoidEachOther
      (retainedTerminalFanOuterLocalRouteAt
        center firstDirection firstSlot)
      (splitRadialRoute center secondTerminal secondSlot) := by
  unfold splitRadialRoute
  exact
    (retainedTerminalFanOuterLocal_strictlyAvoid_radialPrefix
      center firstDirection firstSlot secondSlot secondTerminal
      radialPositive).join_right
      (retainedTerminalFanOuterLocalRouteAt_strictlyAvoid_laterFinalStub
        center firstDirection secondTerminal.1
        firstSlot secondSlot directionsLe slotsLt)
      (retainedTerminalFanOuterRadialPrefix_getLast?
        center secondTerminal secondSlot radialPositive)
      (retainedTerminalFanOuterRadialFinalStubAt_head?
        center secondTerminal.1 secondSlot)

set_option maxRecDepth 4096 in
/-- A cardinal radial route is obtained by coarsening the last two collinear
segments of its explicitly split form. -/
theorem radialRoute_direct_coarsening
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (radialPositive :
      0 < retainedTerminalFanOuterRadialLength terminal)
    (direct : ¬ terminal.1.usesBlockedRaster) :
    ∃ (leading : List Cell) (first middle finish : Cell),
      splitRadialRoute center terminal slot =
          joinAtEndpoint leading [first, middle, finish] ∧
        retainedTerminalFanOuterRadialRoute center terminal slot =
          joinAtEndpoint leading [first, finish] ∧
        leading.getLast? = some first ∧
        (GridSegment.mk first finish).InteriorContains middle := by
  rcases terminal with ⟨direction, length⟩
  cases direction with
  | compass port =>
      let gate :=
        (retainedAngularFanOuterDemand
          center (.compass port, length) slot).gate
      let leading :=
        retainedTerminalFanOuterLaneShiftRouteAt
          gate (.compass port) slot
      let first :=
        Cell.add gate
          (retainedTerminalFanOuterLaneOffset
            (.compass port) slot)
      let middle :=
        Cell.add center
          (Cell.add
            (retainedTerminalFanOuterLanePortOffset
              (.compass port) slot)
            (RetainedTerminalDirection.compass port).primitive)
      let finish :=
        retainedTerminalFanOuterLanePort
          center (.compass port) slot
      refine ⟨leading, first, middle, finish, ?_, ?_, ?_, ?_⟩
      all_goals
        cases port <;>
          simp [
            RetainedTerminalDirection.usesBlockedRaster,
            portUsesDiagonalRaster] at direct
      all_goals
        simp [
          splitRadialRoute,
          retainedTerminalFanOuterRadialPrefix,
          retainedTerminalFanOuterRadialRoute,
          retainedTerminalFanOuterInwardPrefixRay,
          retainedTerminalFanOuterInwardRay,
          retainedTerminalFanOuterRadialFinalStubAt,
          retainedTerminalFanOuterRadialFinalStub,
          RetainedRay.rasterize,
          retainedAngularFanOuterDemand_gate_eq_interface_ray,
          retainedTerminalFanOuterRadialLength,
          retainedTerminalFanTotalRefinement,
          PeriodicEightOccurrenceSplitPositioned.refinementScale,
          retainedTerminalFanRoutingRefinement,
          retainedTerminalInterfaceMultiplier,
          retainedTerminalInterfaceRadialFactor,
          retainedTerminalFanRefinedInterfaceOffset,
          retainedTerminalInterfaceOffset,
          retainedTerminalFanOuterLanePort,
          retainedTerminalFanOuterLanePortOffset,
          retainedTerminalFanOuterLaneOffset,
          retainedTerminalFanOuterLaneStep,
          retainedTerminalFanOuterLaneSpacing,
          RetainedTerminalDirection.primitive,
          OccurrenceSplitRing.Port.unitVector,
          oppositePort, compassRay, joinAtEndpoint,
          GridSegment.InteriorContains,
          GridSegment.IsHorizontal,
          GridSegment.IsVertical,
          GridSegment.StrictlyBetween,
          gate, leading, first, middle, finish,
          Cell.add, Cell.scale] at radialPositive ⊢ <;>
        try omega
      all_goals
        split <;> simp_all <;> omega
  | routedClause arm =>
      simp [RetainedTerminalDirection.usesBlockedRaster] at direct

end PeriodicEightOccurrenceSplit
end LeanTrominoes
