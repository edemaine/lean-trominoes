import LeanTrominoes.RetainedAngularFanOuterCompleteRoutes
import LeanTrominoes.RetainedRayRasterizationCorridor

/-!
# A uniform corridor containing each complete outer fan route

The unbounded part of an outer fan follows its source terminal ray with a
lane offset of at most 56 cells and a rasterization deviation of at most
nine cells.  Its remaining local part stays in the fixed radius-288 square
around the variable center.  This file packages that dichotomy for later
source-prefix/fan cross-separation arguments.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

/-- Coordinate-radius containment composes, adding the two radii. -/
theorem WithinCoordinateRadius.trans
    {firstRadius secondRadius : Nat}
    {firstCenter secondCenter point : Cell}
    (first :
      WithinCoordinateRadius firstRadius
        firstCenter secondCenter)
    (second :
      WithinCoordinateRadius secondRadius
        secondCenter point) :
    WithinCoordinateRadius (firstRadius + secondRadius)
      firstCenter point := by
  rcases firstCenter with ⟨firstX, firstY⟩
  rcases secondCenter with ⟨secondX, secondY⟩
  rcases point with ⟨pointX, pointY⟩
  rcases first with ⟨firstHorizontal, firstVertical⟩
  rcases second with ⟨secondHorizontal, secondVertical⟩
  constructor
  · have decomposition :
        pointX - firstX =
          (secondX - firstX) + (pointX - secondX) := by
      ring
    rw [decomposition]
    exact
      (Int.natAbs_add_le _ _).trans
        (Nat.add_le_add firstHorizontal secondHorizontal)
  · have decomposition :
        pointY - firstY =
          (secondY - firstY) + (pointY - secondY) := by
      ring
    rw [decomposition]
    exact
      (Int.natAbs_add_le _ _).trans
        (Nat.add_le_add firstVertical secondVertical)

/-- Enlarging the radius preserves coordinate-radius containment. -/
theorem WithinCoordinateRadius.mono
    {firstRadius secondRadius : Nat}
    {center point : Cell}
    (bounded :
      WithinCoordinateRadius firstRadius center point)
    (radiusLe : firstRadius ≤ secondRadius) :
    WithinCoordinateRadius secondRadius center point :=
  ⟨bounded.1.trans radiusLe,
    bounded.2.trans radiusLe⟩

/-- A point lies in a coordinate-radius tube around the integral
checkpoints of one directed primitive segment. -/
def InCoordinateCheckpointTube
    (radius : Nat)
    (start primitive : Cell)
    (length : Nat)
    (point : Cell) : Prop :=
  ∃ index : Nat, index ≤ length ∧
    WithinCoordinateRadius radius
      (Cell.add start (Cell.scale index primitive))
      point

instance (radius : Nat) (start primitive : Cell)
    (length : Nat) (point : Cell) :
    Decidable
      (InCoordinateCheckpointTube
        radius start primitive length point) := by
  unfold InCoordinateCheckpointTube
  infer_instance

/-- Every one of the eight tangential lane offsets lies in the radius-56
square around the source gate. -/
theorem retainedTerminalFanOuterLaneOffset_within_radius :
    ∀ (direction : RetainedTerminalDirection)
      (lane : RetainedTerminalSlot),
      WithinCoordinateRadius 56 (0, 0)
        (retainedTerminalFanOuterLaneOffset
          direction lane) := by
  native_decide

/-- Every point of the finite gate-to-lane shift lies in the radius-65 tube
at checkpoint zero. -/
theorem retainedTerminalFanOuterLaneShiftRouteAt_point_in_tube
    (gate : Cell)
    (direction : RetainedTerminalDirection)
    (lane : RetainedTerminalSlot)
    (primitive : Cell)
    (length : Nat)
    {point : Cell}
    (pointMember :
      point ∈
        retainedTerminalFanOuterLaneShiftRouteAt
          gate direction lane) :
    InCoordinateCheckpointTube 65 gate
      primitive length point := by
  unfold retainedTerminalFanOuterLaneShiftRouteAt
    PeriodicOrthocrossing.translatePolyline
    retainedTerminalFanOuterLaneShiftRoute at pointMember
  rw [List.mem_map] at pointMember
  rcases pointMember with
    ⟨offset, offsetMember, rfl⟩
  refine ⟨0, Nat.zero_le _, ?_⟩
  simp only [Cell.scale, Cell.add]
  by_cases laneZero : lane.val = 0
  · simp [laneZero] at offsetMember
    subst offset
    simpa [Cell.add] using
      withinCoordinateRadius_refl 65 gate
  · simp [laneZero] at offsetMember
    rcases offsetMember with rfl | rfl
    · simpa [Cell.add] using
        withinCoordinateRadius_refl 65 gate
    · have bounded :=
        (retainedTerminalFanOuterLaneOffset_within_radius
          direction lane).translate gate
      simpa [Cell.add] using
        bounded.mono (by omega : 56 ≤ 65)

/-- Every point of the complete radial portion lies in a radius-65 tube
around its unshifted retained-ray checkpoints. -/
theorem retainedTerminalFanOuterRadialRoute_point_in_tube
    (center : Cell)
    (terminal : RetainedTerminalData)
    (lane : RetainedTerminalSlot)
    {point : Cell}
    (pointMember :
      point ∈
        retainedTerminalFanOuterRadialRoute
          center terminal lane) :
    let gate :=
      (retainedAngularFanOuterDemand
        center terminal lane).gate
    InCoordinateCheckpointTube 65 gate
      (retainedTerminalFanOuterInwardRay terminal).primitive
      (retainedTerminalFanOuterInwardRay terminal).length
      point := by
  dsimp only
  rw [retainedTerminalFanOuterRadialRoute] at pointMember
  rcases mem_joinAtEndpoint pointMember with
    shiftMember | rayMember
  · exact
      retainedTerminalFanOuterLaneShiftRouteAt_point_in_tube
        (retainedAngularFanOuterDemand
          center terminal lane).gate
        terminal.1 lane
        (retainedTerminalFanOuterInwardRay terminal).primitive
        (retainedTerminalFanOuterInwardRay terminal).length
        shiftMember
  · rcases
        (retainedTerminalFanOuterInwardRay terminal)
          |>.rasterize_point_near_checkpoint
            (Cell.add
              (retainedAngularFanOuterDemand
                center terminal lane).gate
              (retainedTerminalFanOuterLaneOffset
                terminal.1 lane))
            rayMember with
      ⟨index, indexBound, pointNearShifted⟩
    refine ⟨index, indexBound, ?_⟩
    have laneNearUnshifted :
        WithinCoordinateRadius 56
          (Cell.add
            (retainedAngularFanOuterDemand
              center terminal lane).gate
            (Cell.scale index
              (retainedTerminalFanOuterInwardRay
                terminal).primitive))
          (Cell.add
            (Cell.add
              (retainedAngularFanOuterDemand
                center terminal lane).gate
              (retainedTerminalFanOuterLaneOffset
                terminal.1 lane))
            (Cell.scale index
              (retainedTerminalFanOuterInwardRay
                terminal).primitive)) := by
      have translated :=
        (retainedTerminalFanOuterLaneOffset_within_radius
          terminal.1 lane).translate
            (Cell.add
              (retainedAngularFanOuterDemand
                center terminal lane).gate
              (Cell.scale index
                (retainedTerminalFanOuterInwardRay
                  terminal).primitive))
      simpa [Cell.add, add_comm, add_left_comm, add_assoc] using
        translated
    have combined :=
      laneNearUnshifted.trans pointNearShifted
    simpa using combined

/-- Every complete outer-fan point lies either in the radius-65 terminal-ray
tube or in the fixed radius-288 local square around the variable center. -/
theorem retainedTerminalFanOuterCompleteRoute_point_in_corridor
    (center : Cell)
    (terminal : RetainedTerminalData)
    (lane : RetainedTerminalSlot)
    {point : Cell}
    (pointMember :
      point ∈
        retainedTerminalFanOuterCompleteRoute
          center terminal lane) :
    let gate :=
      (retainedAngularFanOuterDemand
        center terminal lane).gate
    InCoordinateCheckpointTube 65 gate
        (retainedTerminalFanOuterInwardRay terminal).primitive
        (retainedTerminalFanOuterInwardRay terminal).length
        point ∨
      WithinCoordinateRadius 288 center point := by
  dsimp only
  rw [retainedTerminalFanOuterCompleteRoute] at pointMember
  rcases mem_joinAtEndpoint pointMember with
    radialMember | localMember
  · exact Or.inl
      (retainedTerminalFanOuterRadialRoute_point_in_tube
        center terminal lane radialMember)
  · right
    rw [retainedTerminalFanOuterLocalRouteAt,
      List.mem_map] at localMember
    rcases localMember with
      ⟨offset, offsetMember, rfl⟩
    have localBound :=
      retainedTerminalFanOuterLocalRoute_points_within_outer_frame
        terminal.1 lane offset offsetMember
    have translated := localBound.translate center
    simpa [Cell.add] using translated

end PeriodicEightOccurrenceSplit
end LeanTrominoes
