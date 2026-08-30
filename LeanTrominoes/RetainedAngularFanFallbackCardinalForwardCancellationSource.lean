/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BoundedDelimitedDirectionCancellationOutAndBack
import LeanTrominoes.RetainedAngularFanFallbackCardinalForwardCancellationDirections

/-! # Kept source words at a forward-cardinal cancellation junction -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing
open PeriodicOrthocrossing

/-- Unit route retained through the shifted gate, including that gate. -/
def retainedFallbackCardinalForwardKeptRoute
    (route : List Cell)
    (port : Port)
    (length : Nat)
    (slot : RetainedTerminalSlot)
    (distance : Nat) : List Cell :=
  let path := retainedTerminalFanCardinalForwardOverlapPath
    (retainedFallbackFanCenter route) port length slot
  retainedFallbackCardinalForwardLeadingPoints
      route port length slot distance ++
    [path.head
      (retainedTerminalFanCardinalForwardOverlapPath_ne_nil
        (retainedFallbackFanCenter route) port length slot)]

def retainedFallbackCardinalForwardKeptDirections
    (route : List Cell)
    (port : Port)
    (length : Nat)
    (slot : RetainedTerminalSlot)
    (distance : Nat) : List AxisDirection :=
  Gadget.unitSubdivisionDirections
    (retainedFallbackCardinalForwardKeptRoute
      route port length slot distance)

/-- Finite counter representing one occurrence-lane displacement. -/
def retainedTerminalFanCardinalCancellationCount
    (slot : RetainedTerminalSlot) :
    BoundedDelimitedDirectionCancellation.Count :=
  ⟨retainedTerminalFanOuterLaneSpacing * slot.val, by
    unfold retainedTerminalFanOuterLaneSpacing
      BoundedDelimitedDirectionCancellation.bufferCapacity
    omega⟩

@[simp] theorem retainedTerminalFanCardinalCancellationCount_val
    (slot : RetainedTerminalSlot) :
    (retainedTerminalFanCardinalCancellationCount slot).val =
      retainedTerminalFanOuterLaneSpacing * slot.val :=
  rfl

/-- The kept point route is exactly the unit subdivision of the adjusted
source prefix; that adjusted route remains nondegenerate, orthogonal, and
ends in the forward tangent direction. -/
theorem retainedFallbackCardinalForwardKeptRoute_data
    (route : List Cell)
    (port : Port)
    (length : Nat)
    (slot : RetainedTerminalSlot)
    (distance : Nat)
    (routeLength : 3 ≤ route.length)
    (routeOrthogonal : OrthogonalPolyline route)
    (cardinal :
      port = .north ∨ port = .east ∨
        port = .south ∨ port = .west)
    (shiftStrict :
      retainedTerminalFanOuterLaneSpacing * slot.val < distance)
    (predecessor :
      (retainedFallbackSourcePrefix route).dropLast.getLast? =
        some
          (Cell.add
            (retainedAngularFanOuterDemand
              (retainedFallbackFanCenter route)
              (.compass port, length) slot).gate
            (Cell.scale distance
              (retainedTerminalFanOuterLaneStep
                (.compass port))))) :
    let adjusted :=
      retainedFallbackCardinalForwardAdjustedSourceRoute
        route port length slot distance
    retainedFallbackCardinalForwardKeptRoute
        route port length slot distance =
      AxisDirection.unitSubdividePolyline adjusted ∧
    2 ≤ adjusted.length ∧
    OrthogonalPolyline adjusted ∧
    AxisDirection.polylineLastDirection adjusted =
      retainedTerminalFanCardinalForwardDirection port := by
  let sourcePrefix := retainedFallbackSourcePrefix route
  let sourceLeading := sourcePrefix.dropLast
  let center := retainedFallbackFanCenter route
  let gate :=
    (retainedAngularFanOuterDemand
      center (.compass port, length) slot).gate
  let shiftedGate := Cell.add gate
    (retainedTerminalFanOuterLaneOffset (.compass port) slot)
  let tangentLeading :=
    retainedTerminalFanCardinalForwardTangentLeadingRoute
      center port length slot distance
  let adjusted :=
    retainedFallbackCardinalForwardAdjustedSourceRoute
      route port length slot distance
  let path := retainedTerminalFanCardinalForwardOverlapPath
    center port length slot
  let overlapRoute :=
    retainedTerminalFanCardinalForwardTangentOverlapRoute
      center port length slot
  have routeLengthTwo : 2 ≤ route.length := by omega
  have sourcePrefixOrthogonal : OrthogonalPolyline sourcePrefix := by
    exact (routeOrthogonal.scalePolyline (by native_decide)).dropLast
  have sourcePrefixLength : 2 ≤ sourcePrefix.length := by
    dsimp [sourcePrefix, retainedFallbackSourcePrefix]
    rw [List.length_dropLast]
    simpa [scalePolyline] using
      (show 2 ≤ route.length - 1 by omega)
  have sourceLeadingLength : 0 < sourceLeading.length := by
    dsimp [sourceLeading]
    rw [List.length_dropLast]
    omega
  have sourceLeadingNonempty : sourceLeading ≠ [] :=
    List.ne_nil_of_length_pos sourceLeadingLength
  have sourceLeadingOrthogonal : OrthogonalPolyline sourceLeading :=
    sourcePrefixOrthogonal.dropLast
  have sourceLeadingLast : sourceLeading.getLast? =
      some
        (Cell.add gate
          (Cell.scale distance
            (retainedTerminalFanOuterLaneStep (.compass port)))) := by
    simpa [sourceLeading, sourcePrefix, center, gate] using predecessor
  have tangentLeadingHead : tangentLeading.head? =
      some
        (Cell.add gate
          (Cell.scale distance
            (retainedTerminalFanOuterLaneStep (.compass port)))) := by
    simp [tangentLeading, gate]
  have tangentLeadingLast : tangentLeading.getLast? =
      some shiftedGate := by
    simp [tangentLeading, shiftedGate, gate]
  have tangentLeadingLength : 2 ≤ tangentLeading.length := by
    simp [tangentLeading,
      retainedTerminalFanCardinalForwardTangentLeadingRoute]
  have tangentLeadingOrthogonal : OrthogonalPolyline tangentLeading :=
    retainedTerminalFanCardinalForwardTangentLeadingRoute_orthogonal
      center port length slot distance cardinal shiftStrict
  have adjustedEq :
      adjusted = joinAtEndpoint sourceLeading tangentLeading := by
    rfl
  have adjustedNonempty : adjusted ≠ [] := by
    rw [adjustedEq]
    intro empty
    unfold joinAtEndpoint at empty
    exact sourceLeadingNonempty (List.append_eq_nil_iff.mp empty).1
  have adjustedOrthogonal : OrthogonalPolyline adjusted := by
    rw [adjustedEq]
    exact sourceLeadingOrthogonal.joinAtEndpoint tangentLeadingOrthogonal
      sourceLeadingLast tangentLeadingHead
  have adjustedLength : 2 ≤ adjusted.length := by
    rw [adjustedEq]
    unfold joinAtEndpoint
    simp only [List.length_append, List.length_tail]
    omega
  have adjustedLast : adjusted.getLast? = some shiftedGate := by
    rw [adjustedEq]
    exact joinAtEndpoint_getLast?
      sourceLeadingLast tangentLeadingHead tangentLeadingLast
  have adjustedUnitLast :
      (AxisDirection.unitSubdividePolyline adjusted).getLast? =
        some shiftedGate := by
    rw [AxisDirection.unitSubdividePolyline_getLast?
      adjustedNonempty adjustedOrthogonal, adjustedLast]
  have pathNonempty : path ≠ [] :=
    retainedTerminalFanCardinalForwardOverlapPath_ne_nil
      center port length slot
  have overlapRouteHead : overlapRoute.head? = some shiftedGate := by
    simp [overlapRoute, shiftedGate, gate]
  have overlapRouteNonempty : overlapRoute ≠ [] := by
    intro empty
    rw [empty] at overlapRouteHead
    simp at overlapRouteHead
  have pathHead : path.head? = some shiftedGate := by
    unfold path retainedTerminalFanCardinalForwardOverlapPath
    rw [AxisDirection.unitSubdividePolyline_head?
      overlapRouteNonempty, overlapRouteHead]
  have keptEq :
      retainedFallbackCardinalForwardKeptRoute
          route port length slot distance =
        AxisDirection.unitSubdividePolyline adjusted := by
    unfold retainedFallbackCardinalForwardKeptRoute
      retainedFallbackCardinalForwardLeadingPoints
    change
      (AxisDirection.unitSubdividePolyline adjusted).dropLast ++
          [path.head pathNonempty] =
        AxisDirection.unitSubdividePolyline adjusted
    have headEq : path.head pathNonempty = shiftedGate := by
      exact Option.some.inj
        ((List.head?_eq_some_head pathNonempty).symm.trans pathHead)
    rw [headEq]
    exact List.dropLast_append_getLast? shiftedGate adjustedUnitLast
  have adjustedLastDirection :
      AxisDirection.polylineLastDirection adjusted =
        retainedTerminalFanCardinalForwardDirection port := by
    rw [adjustedEq,
      AxisDirection.polylineLastDirection_joinAtEndpoint
        sourceLeadingLast tangentLeadingHead tangentLeadingLength]
    exact
      retainedTerminalFanCardinalForwardTangentLeadingRoute_lastDirection
        center port length slot distance cardinal shiftStrict
  exact ⟨keptEq, adjustedLength, adjustedOrthogonal,
    adjustedLastDirection⟩

/-- Source-prefix directions split into the kept word and one constant
bounded overlap block. -/
theorem retainedFallbackSourcePrefix_forward_directions
    (route : List Cell)
    (port : Port)
    (length : Nat)
    (slot : RetainedTerminalSlot)
    (distance : Nat)
    (routeLength : 3 ≤ route.length)
    (classified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector route) =
        some (.compass port, length))
    (routeOrthogonal : OrthogonalPolyline route)
    (cardinal :
      port = .north ∨ port = .east ∨
        port = .south ∨ port = .west)
    (shiftStrict :
      retainedTerminalFanOuterLaneSpacing * slot.val < distance)
    (predecessor :
      (retainedFallbackSourcePrefix route).dropLast.getLast? =
        some
          (Cell.add
            (retainedAngularFanOuterDemand
              (retainedFallbackFanCenter route)
              (.compass port, length) slot).gate
            (Cell.scale distance
              (retainedTerminalFanOuterLaneStep
                (.compass port))))) :
    Gadget.unitSubdivisionDirections
        (retainedFallbackSourcePrefix route) =
      retainedFallbackCardinalForwardKeptDirections
          route port length slot distance ++
        List.replicate
          (retainedTerminalFanCardinalCancellationCount slot).val
          (retainedTerminalFanCardinalForwardDirection port) := by
  let sourcePrefix := retainedFallbackSourcePrefix route
  let center := retainedFallbackFanCenter route
  let leading := retainedFallbackCardinalForwardLeadingPoints
    route port length slot distance
  let path := retainedTerminalFanCardinalForwardOverlapPath
    center port length slot
  have sourcePrefixOrthogonal : OrthogonalPolyline sourcePrefix :=
    (routeOrthogonal.scalePolyline (by native_decide)).dropLast
  have pathNonempty : path ≠ [] :=
    retainedTerminalFanCardinalForwardOverlapPath_ne_nil
      center port length slot
  have subdivision :
      AxisDirection.unitSubdividePolyline sourcePrefix =
        leading ++ path := by
    simpa [sourcePrefix, center, leading, path] using
      retainedFallbackSourcePrefix_unitSubdivide_eq_forwardLeading_append_overlap
        route port length slot distance routeLength classified
        routeOrthogonal cardinal shiftStrict predecessor
  have split :=
    BoundedDelimitedDirectionCancellation.unitSubdivisionDirections_eq_kept_append_path
      sourcePrefix leading path sourcePrefixOrthogonal pathNonempty
      subdivision
  have overlapDirections :=
    retainedTerminalFanCardinalForwardOverlapPath_directions
      center port length slot cardinal
  rw [overlapDirections] at split
  simpa [sourcePrefix, leading, path,
    retainedFallbackCardinalForwardKeptDirections,
    retainedFallbackCardinalForwardKeptRoute] using split

/-- Trimming the overlap length from the source word leaves exactly the
kept prefix word. -/
theorem retainedFallbackSourcePrefix_forward_take
    (route : List Cell)
    (port : Port)
    (length : Nat)
    (slot : RetainedTerminalSlot)
    (distance : Nat)
    (routeLength : 3 ≤ route.length)
    (classified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector route) =
        some (.compass port, length))
    (routeOrthogonal : OrthogonalPolyline route)
    (cardinal :
      port = .north ∨ port = .east ∨
        port = .south ∨ port = .west)
    (shiftStrict :
      retainedTerminalFanOuterLaneSpacing * slot.val < distance)
    (predecessor :
      (retainedFallbackSourcePrefix route).dropLast.getLast? =
        some
          (Cell.add
            (retainedAngularFanOuterDemand
              (retainedFallbackFanCenter route)
              (.compass port, length) slot).gate
            (Cell.scale distance
              (retainedTerminalFanOuterLaneStep
                (.compass port))))) :
    (Gadget.unitSubdivisionDirections
        (retainedFallbackSourcePrefix route)).take
        ((Gadget.unitSubdivisionDirections
            (retainedFallbackSourcePrefix route)).length -
          (retainedTerminalFanCardinalCancellationCount slot).val) =
      retainedFallbackCardinalForwardKeptDirections
        route port length slot distance := by
  rw [retainedFallbackSourcePrefix_forward_directions
    route port length slot distance routeLength classified
    routeOrthogonal cardinal shiftStrict predecessor]
  simp

/-- The kept direction word is nonempty and ends in the overlap direction. -/
theorem retainedFallbackCardinalForwardKeptDirections_getLast?
    (route : List Cell)
    (port : Port)
    (length : Nat)
    (slot : RetainedTerminalSlot)
    (distance : Nat)
    (routeLength : 3 ≤ route.length)
    (routeOrthogonal : OrthogonalPolyline route)
    (cardinal :
      port = .north ∨ port = .east ∨
        port = .south ∨ port = .west)
    (shiftStrict :
      retainedTerminalFanOuterLaneSpacing * slot.val < distance)
    (predecessor :
      (retainedFallbackSourcePrefix route).dropLast.getLast? =
        some
          (Cell.add
            (retainedAngularFanOuterDemand
              (retainedFallbackFanCenter route)
              (.compass port, length) slot).gate
            (Cell.scale distance
              (retainedTerminalFanOuterLaneStep
                (.compass port))))) :
    (retainedFallbackCardinalForwardKeptDirections
      route port length slot distance).getLast? =
        some (retainedTerminalFanCardinalForwardDirection port) := by
  let adjusted :=
    retainedFallbackCardinalForwardAdjustedSourceRoute
      route port length slot distance
  have data := retainedFallbackCardinalForwardKeptRoute_data
    route port length slot distance routeLength
    routeOrthogonal cardinal shiftStrict predecessor
  have adjustedLast :=
    BoundedDelimitedDirectionCancellation.unitSubdivisionDirections_getLast?
      adjusted data.2.1 data.2.2.1
  unfold retainedFallbackCardinalForwardKeptDirections
  rw [data.1,
    Gadget.unitSubdivisionDirections_unitSubdividePolyline
      adjusted data.2.2.1,
    adjustedLast, data.2.2.2]

end PeriodicEightOccurrenceSplit
end LeanTrominoes
