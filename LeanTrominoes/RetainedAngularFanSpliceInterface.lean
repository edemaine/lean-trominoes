import LeanTrominoes.RetainedAngularFanPositionedRoutes
import LeanTrominoes.RetainedAngularTerminalInterfaceGeometry
import LeanTrominoes.RetainedAngularTerminalSlotLookup

/-!
# Exact source-to-fan splice interface

The retained source first receives the factor-36 Figure 7 refinement and the
finite fan router then receives its factor-eight refinement.  Their combined
factor is 288.  At that scale, every classified source gate is a positive
radial multiple of a fixed radius-288 direction interface, while the
positioned certified fan route begins at its exact radius-264 fan port.

This file packages those two points as the outer-adapter demand for one
occurrence.  It also proves that looking up a genuine source occurrence in
its angular slot selects the demand carrying its exact classified terminal
datum.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicThreeSATThree

/-- Combined source and finite-router refinement used at the final splice. -/
def retainedTerminalFanTotalRefinement : Nat :=
  PeriodicEightOccurrenceSplitPositioned.refinementScale.toNat *
    retainedTerminalFanRoutingRefinement

@[simp]
theorem retainedTerminalFanTotalRefinement_eq :
    retainedTerminalFanTotalRefinement = 288 := by
  native_decide

/-- Factor-eight refinement of one fixed radius-36 direction interface. -/
def retainedTerminalFanRefinedInterfaceOffset
    (direction : RetainedTerminalDirection) : Cell :=
  Cell.scale retainedTerminalFanRoutingRefinement
    (retainedTerminalInterfaceOffset direction)

/-- Every refined direction interface lies exactly on the radius-288
square. -/
theorem retainedTerminalFanRefinedInterfaceOffset_on_square
    (direction : RetainedTerminalDirection) :
    WithinCoordinateRadius
        (36 * retainedTerminalFanRoutingRefinement)
        (0, 0)
        (retainedTerminalFanRefinedInterfaceOffset direction) ∧
      ¬ WithinCoordinateRadius
        (36 * retainedTerminalFanRoutingRefinement - 1)
        (0, 0)
        (retainedTerminalFanRefinedInterfaceOffset direction) := by
  cases direction with
  | compass port =>
      cases port <;>
        native_decide
  | routedClause arm =>
      cases arm <;>
        native_decide

/-- Distinct retained directions still have distinct refined interface
points. -/
theorem retainedTerminalFanRefinedInterfaceOffset_injective :
    Function.Injective
      retainedTerminalFanRefinedInterfaceOffset := by
  intro first second equal
  apply retainedTerminalInterfaceOffset_injective
  apply Prod.ext
  · have horizontal := congrArg Prod.fst equal
    simp [retainedTerminalFanRefinedInterfaceOffset,
      retainedTerminalFanRoutingRefinement,
      Cell.scale] at horizontal
    omega
  · have vertical := congrArg Prod.snd equal
    simp [retainedTerminalFanRefinedInterfaceOffset,
      retainedTerminalFanRoutingRefinement,
      Cell.scale] at vertical
    omega

/-- At the combined refinement, terminal displacement is a radial multiple
of the refined fixed direction interface. -/
theorem scaleRetainedTerminalData_total_displacement_eq_refined_interface
    (terminal : RetainedTerminalData) :
    Cell.scale
        (scaleRetainedTerminalData
          retainedTerminalFanTotalRefinement terminal).2
        terminal.1.primitive =
      Cell.scale
        (retainedTerminalInterfaceRadialFactor terminal)
        (retainedTerminalFanRefinedInterfaceOffset terminal.1) := by
  rcases terminal with ⟨direction, length⟩
  cases direction with
  | compass port =>
      cases port <;>
        simp [scaleRetainedTerminalData,
          retainedTerminalFanTotalRefinement,
          PeriodicEightOccurrenceSplitPositioned.refinementScale,
          retainedTerminalFanRoutingRefinement,
          retainedTerminalInterfaceRadialFactor,
          retainedTerminalFanRefinedInterfaceOffset,
          retainedTerminalInterfaceOffset,
          retainedTerminalInterfaceMultiplier,
          RetainedTerminalDirection.primitive,
          OccurrenceSplitRing.Port.unitVector,
          Cell.scale] <;>
        ring
  | routedClause arm =>
      cases arm <;>
        simp [scaleRetainedTerminalData,
          retainedTerminalFanTotalRefinement,
          PeriodicEightOccurrenceSplitPositioned.refinementScale,
          retainedTerminalFanRoutingRefinement,
          retainedTerminalInterfaceRadialFactor,
          retainedTerminalFanRefinedInterfaceOffset,
          retainedTerminalInterfaceOffset,
          retainedTerminalInterfaceMultiplier,
          RetainedTerminalDirection.primitive,
          routedClauseRayPrimitive,
          Cell.sub, Cell.scale] <;>
        omega

/-- Exact endpoints requested from the outer adapter for one classified
source occurrence. -/
@[ext]
structure RetainedAngularFanOuterDemand where
  gate : Cell
  fanPort : Cell
  deriving DecidableEq, Repr

/-- Outer-adapter demand at an already refined variable center. -/
def retainedAngularFanOuterDemand
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot) :
    RetainedAngularFanOuterDemand where
  gate :=
    retainedTerminalSplicePoint center
      (scaleRetainedTerminalData
        retainedTerminalFanTotalRefinement terminal)
  fanPort :=
    Cell.add center
      (Cell.scale retainedTerminalFanRoutingRefinement
        (retainedTerminalFanPortOffset
          (retainedTerminalFanPort terminal.1 slot)))

/-- The demand gate is exactly the advertised radial multiple of the
refined direction interface. -/
theorem retainedAngularFanOuterDemand_gate_eq_interface_ray
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot) :
    (retainedAngularFanOuterDemand center terminal slot).gate =
      Cell.add center
        (Cell.scale
          (retainedTerminalInterfaceRadialFactor terminal)
          (retainedTerminalFanRefinedInterfaceOffset terminal.1)) := by
  simp only [retainedAngularFanOuterDemand,
    retainedTerminalSplicePoint,
    scaleRetainedTerminalData_direction]
  rw [
    scaleRetainedTerminalData_total_displacement_eq_refined_interface]

/-- Reconstructing a demand from a classified source route makes its gate
exactly the penultimate point of that route after the combined refinement. -/
theorem polylineLastEntrance_scalePolyline_eq_outerDemand_gate
    {route : List Cell}
    (routeLength : 2 ≤ route.length)
    {terminal : RetainedTerminalData}
    (classified :
      retainedTerminalDirectionClassify
          (routeTerminalVector route) =
        some terminal)
    (slot : RetainedTerminalSlot) :
    polylineLastEntrance
        (scalePolyline retainedTerminalFanTotalRefinement route) =
      (retainedAngularFanOuterDemand
        (Cell.scale retainedTerminalFanTotalRefinement
          (route.getLastD (0, 0)))
        terminal slot).gate := by
  have scaledLength :
      2 ≤
        (scalePolyline
          retainedTerminalFanTotalRefinement route).length := by
    simpa [scalePolyline] using routeLength
  rw [polylineLastEntrance_eq_retainedTerminalSplicePoint
    scaledLength
    (routeTerminalVector_scale_classified
      (by native_decide)
      classified)]
  rw [scalePolyline_getLastD]
  rfl

/-- Every positive demand gate lies outside the refined Figure 7 interior. -/
theorem retainedAngularFanOuterDemand_gate_outside_fan
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (lengthPositive : 0 < terminal.2) :
    ¬ WithinCoordinateRadius
      (12 * retainedTerminalFanRoutingRefinement - 1)
      center
      (retainedAngularFanOuterDemand center terminal slot).gate := by
  rcases center with ⟨centerX, centerY⟩
  rcases terminal with ⟨direction, length⟩
  cases direction with
  | compass port =>
      cases port <;>
        simp [retainedAngularFanOuterDemand,
          retainedTerminalSplicePoint,
          scaleRetainedTerminalData,
          retainedTerminalFanTotalRefinement,
          PeriodicEightOccurrenceSplitPositioned.refinementScale,
          retainedTerminalFanRoutingRefinement,
          RetainedTerminalDirection.primitive,
          OccurrenceSplitRing.Port.unitVector,
          WithinCoordinateRadius, Cell.add, Cell.scale] <;>
        omega
  | routedClause arm =>
      cases arm <;>
        simp [retainedAngularFanOuterDemand,
          retainedTerminalSplicePoint,
          scaleRetainedTerminalData,
          retainedTerminalFanTotalRefinement,
          PeriodicEightOccurrenceSplitPositioned.refinementScale,
          retainedTerminalFanRoutingRefinement,
          RetainedTerminalDirection.primitive,
          routedClauseRayPrimitive,
          WithinCoordinateRadius,
          Cell.add, Cell.sub, Cell.scale] <;>
        omega

/-- The positioned certified inner route begins at the exact fan-port end
of its outer-adapter demand. -/
theorem retainedTerminalFanRefinedRouteAt_head?_eq_outerDemand
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot) :
    (retainedTerminalFanRefinedRouteAt
      center terminal.1 slot).head? =
        some
          (retainedAngularFanOuterDemand
            center terminal slot).fanPort := by
  simp [retainedAngularFanOuterDemand]

/-- Optional outer demand selected by one concrete profile slot. -/
def RetainedAngularTerminalProfile.outerDemand
    (profile : RetainedAngularTerminalProfile)
    (center : Cell)
    (slot : RetainedTerminalSlot) :
    Option RetainedAngularFanOuterDemand :=
  profile.terminals[slot.val]?.map fun terminal =>
    retainedAngularFanOuterDemand center terminal slot

/-- Exact demand selected by a profile lookup. -/
theorem RetainedAngularTerminalProfile.outerDemand_eq_some
    (profile : RetainedAngularTerminalProfile)
    (center : Cell)
    (slot : RetainedTerminalSlot)
    (terminal : RetainedTerminalData)
    (terminalLookup :
      profile.terminals[slot.val]? = some terminal) :
    profile.outerDemand center slot =
      some
        (retainedAngularFanOuterDemand
          center terminal slot) := by
  simp [outerDemand, terminalLookup]

/-- Looking up a genuine occurrence selects the outer demand carrying its
exact classified source terminal datum. -/
theorem retainedAngularTerminalProfile_outerDemand_slot
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (certificate :
      RetainedOccurrenceTerminalCertificate source routes)
    (fits : FitsEightSlots (angularOccurrenceOrder source routes))
    (atom : Variable)
    (copy : ThreeOccurrenceVariable Variable)
    (copyMember : copy ∈ occurrenceVariables source atom)
    (center : Cell) :
    let profile :=
      retainedAngularTerminalProfile
        source routes certificate fits atom
    let slot :=
      retainedAngularTerminalSlot
        source routes fits atom copy copyMember
    profile.outerDemand center slot =
      some
        (retainedAngularFanOuterDemand center
          (classifiedRetainedTerminalData
            (occurrenceTerminalVector routes copy))
          slot) := by
  dsimp only
  apply
    RetainedAngularTerminalProfile.outerDemand_eq_some
  exact
    retainedAngularTerminalProfile_getElem_slot
      source routes certificate fits atom copy copyMember

end PeriodicEightOccurrenceSplit
end LeanTrominoes
