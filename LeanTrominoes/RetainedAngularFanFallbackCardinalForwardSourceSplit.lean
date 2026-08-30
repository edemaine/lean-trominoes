/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFallbackCardinalForwardSuffixSplit
import LeanTrominoes.RetainedAngularFanFallbackSourceSuffixSeparation

/-! # Splitting forward-cardinal source prefixes at the shifted gate -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing
open PeriodicOrthocrossing

/-- Source prefix retained through the shifted gate, before traversing the
ordinary lane-shift overlap. -/
def retainedFallbackCardinalForwardAdjustedSourceRoute
    (route : List Cell)
    (port : Port)
    (length : Nat)
    (slot : RetainedTerminalSlot)
    (distance : Nat) : List Cell :=
  joinAtEndpoint
    (retainedFallbackSourcePrefix route).dropLast
    (retainedTerminalFanCardinalForwardTangentLeadingRoute
      (retainedFallbackFanCenter route)
      port length slot distance)

/-- Unit points strictly before the shifted gate in the adjusted source
prefix. -/
def retainedFallbackCardinalForwardLeadingPoints
    (route : List Cell)
    (port : Port)
    (length : Nat)
    (slot : RetainedTerminalSlot)
    (distance : Nat) : List Cell :=
  (AxisDirection.unitSubdividePolyline
    (retainedFallbackCardinalForwardAdjustedSourceRoute
      route port length slot distance)).dropLast

/-- A source prefix whose final segment approaches from the forward
tangential side splits into the kept unit prefix and the backward lane-shift
overlap. -/
theorem retainedFallbackSourcePrefix_unitSubdivide_eq_forwardLeading_append_overlap
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
    AxisDirection.unitSubdividePolyline
        (retainedFallbackSourcePrefix route) =
      retainedFallbackCardinalForwardLeadingPoints
          route port length slot distance ++
        retainedTerminalFanCardinalForwardOverlapPath
          (retainedFallbackFanCenter route)
          port length slot := by
  let sourcePrefix := retainedFallbackSourcePrefix route
  let sourceLeading := sourcePrefix.dropLast
  let center := retainedFallbackFanCenter route
  let gate :=
    (retainedAngularFanOuterDemand
      center (.compass port, length) slot).gate
  let shiftedGate := Cell.add gate
    (retainedTerminalFanOuterLaneOffset (.compass port) slot)
  let tangent := retainedTerminalFanCardinalForwardTangentRoute
    center port length slot distance
  let tangentLeading :=
    retainedTerminalFanCardinalForwardTangentLeadingRoute
      center port length slot distance
  let overlap := retainedTerminalFanCardinalForwardTangentOverlapRoute
    center port length slot
  let splitTangent :=
    retainedTerminalFanCardinalForwardTangentSplitRoute
      center port length slot distance
  let adjustedSource :=
    retainedFallbackCardinalForwardAdjustedSourceRoute
      route port length slot distance
  have routeLengthTwo : 2 ≤ route.length := by omega
  have sourcePrefixOrthogonal : OrthogonalPolyline sourcePrefix := by
    exact (routeOrthogonal.scalePolyline (by native_decide)).dropLast
  have sourcePrefixLength : 2 ≤ sourcePrefix.length := by
    dsimp [sourcePrefix, retainedFallbackSourcePrefix]
    rw [List.length_dropLast]
    simpa [scalePolyline] using
      (show 2 ≤ route.length - 1 by omega)
  have sourcePrefixNonempty : sourcePrefix ≠ [] :=
    List.ne_nil_of_length_pos (by omega)
  have sourceLeadingLength : 0 < sourceLeading.length := by
    dsimp [sourceLeading]
    rw [List.length_dropLast]
    omega
  have sourceLeadingNonempty : sourceLeading ≠ [] :=
    List.ne_nil_of_length_pos sourceLeadingLength
  have sourceLeadingOrthogonal : OrthogonalPolyline sourceLeading :=
    sourcePrefixOrthogonal.dropLast
  have sourcePrefixLast : sourcePrefix.getLast? = some gate := by
    simpa [sourcePrefix, center, gate,
      retainedFallbackSourcePrefix, retainedFallbackFanCenter] using
      retainedAngularFanSourcePrefix_getLast?_eq_outerDemand_gate
        route (.compass port, length) slot routeLengthTwo classified
  have tangentHead : tangent.head? =
      some
        (Cell.add gate
          (Cell.scale distance
            (retainedTerminalFanOuterLaneStep (.compass port)))) := by
    simp [tangent, gate]
  have sourceLeadingLast : sourceLeading.getLast? = tangent.head? := by
    simpa [sourceLeading, sourcePrefix, center, tangent, gate] using
      predecessor
  have tangentNonempty : tangent ≠ [] := by
    simp [tangent, retainedTerminalFanCardinalForwardTangentRoute]
  have tangentOrthogonal : OrthogonalPolyline tangent :=
    retainedTerminalFanCardinalForwardTangentRoute_orthogonal
      center port length slot distance cardinal (by omega)
  have prefixSplit :
      sourcePrefix = joinAtEndpoint sourceLeading tangent := by
    calc
      sourcePrefix = sourcePrefix.dropLast ++ [gate] :=
        (List.dropLast_append_getLast? gate sourcePrefixLast).symm
      _ = joinAtEndpoint sourceLeading tangent := by
        simp [joinAtEndpoint, sourceLeading, tangent, gate,
          retainedTerminalFanCardinalForwardTangentRoute]
  have tangentLeadingNonempty : tangentLeading ≠ [] := by
    simp [tangentLeading,
      retainedTerminalFanCardinalForwardTangentLeadingRoute]
  have tangentLeadingOrthogonal : OrthogonalPolyline tangentLeading :=
    retainedTerminalFanCardinalForwardTangentLeadingRoute_orthogonal
      center port length slot distance cardinal shiftStrict
  have sourceLeadingLastPoint : sourceLeading.getLast? =
      some
        (Cell.add gate
          (Cell.scale distance
            (retainedTerminalFanOuterLaneStep (.compass port)))) := by
    rw [sourceLeadingLast, tangentHead]
  have tangentLeadingHead : tangentLeading.head? =
      some
        (Cell.add gate
          (Cell.scale distance
            (retainedTerminalFanOuterLaneStep (.compass port)))) := by
    simp [tangentLeading, gate]
  have tangentLeadingLast : tangentLeading.getLast? = some shiftedGate := by
    simp [tangentLeading, shiftedGate, gate]
  have overlapHead : overlap.head? = some shiftedGate := by
    simp [overlap, shiftedGate, gate]
  have overlapNonempty : overlap ≠ [] := by
    intro empty
    rw [empty] at overlapHead
    simp at overlapHead
  have overlapOrthogonal : OrthogonalPolyline overlap :=
    retainedTerminalFanCardinalForwardTangentOverlapRoute_orthogonal
      center port length slot
  have splitTangentSubdivision :
      AxisDirection.unitSubdividePolyline splitTangent =
        joinAtEndpoint
          (AxisDirection.unitSubdividePolyline tangentLeading)
          (AxisDirection.unitSubdividePolyline overlap) := by
    change AxisDirection.unitSubdividePolyline
        (joinAtEndpoint tangentLeading overlap) = _
    exact AxisDirection.unitSubdividePolyline_joinAtEndpoint
      tangentLeadingNonempty tangentLeadingLast overlapHead
  have tangentSubdivision :
      AxisDirection.unitSubdividePolyline tangent =
        AxisDirection.unitSubdividePolyline splitTangent :=
    retainedTerminalFanCardinalForwardTangentRoute_unitSubdivide_eq_split
      center port length slot distance cardinal shiftStrict
  have sourceSubdivision :
      AxisDirection.unitSubdividePolyline sourcePrefix =
        joinAtEndpoint
          (AxisDirection.unitSubdividePolyline sourceLeading)
          (AxisDirection.unitSubdividePolyline tangent) := by
    rw [prefixSplit]
    exact AxisDirection.unitSubdividePolyline_joinAtEndpoint
      sourceLeadingNonempty sourceLeadingLast tangentHead
  have adjustedSourceEq :
      adjustedSource = joinAtEndpoint sourceLeading tangentLeading := by
    rfl
  have adjustedSourceNonempty : adjustedSource ≠ [] := by
    rw [adjustedSourceEq]
    intro empty
    unfold joinAtEndpoint at empty
    exact sourceLeadingNonempty (List.append_eq_nil_iff.mp empty).1
  have adjustedSourceOrthogonal : OrthogonalPolyline adjustedSource := by
    rw [adjustedSourceEq]
    exact sourceLeadingOrthogonal.joinAtEndpoint tangentLeadingOrthogonal
      sourceLeadingLastPoint tangentLeadingHead
  have adjustedSubdivision :
      AxisDirection.unitSubdividePolyline adjustedSource =
        joinAtEndpoint
          (AxisDirection.unitSubdividePolyline sourceLeading)
          (AxisDirection.unitSubdividePolyline tangentLeading) := by
    rw [adjustedSourceEq]
    exact AxisDirection.unitSubdividePolyline_joinAtEndpoint
      sourceLeadingNonempty sourceLeadingLastPoint tangentLeadingHead
  have adjustedLast : adjustedSource.getLast? = some shiftedGate := by
    rw [adjustedSourceEq]
    exact joinAtEndpoint_getLast?
      sourceLeadingLastPoint tangentLeadingHead tangentLeadingLast
  have adjustedUnitLast :
      (AxisDirection.unitSubdividePolyline adjustedSource).getLast? =
        some shiftedGate := by
    rw [AxisDirection.unitSubdividePolyline_getLast?
      adjustedSourceNonempty adjustedSourceOrthogonal, adjustedLast]
  have overlapUnitHead :
      (AxisDirection.unitSubdividePolyline overlap).head? =
        some shiftedGate := by
    rw [AxisDirection.unitSubdividePolyline_head? overlapNonempty,
      overlapHead]
  calc
    AxisDirection.unitSubdividePolyline sourcePrefix =
        joinAtEndpoint
          (AxisDirection.unitSubdividePolyline sourceLeading)
          (AxisDirection.unitSubdividePolyline tangent) := sourceSubdivision
    _ = joinAtEndpoint
          (AxisDirection.unitSubdividePolyline sourceLeading)
          (AxisDirection.unitSubdividePolyline splitTangent) := by
      rw [tangentSubdivision]
    _ = joinAtEndpoint
          (AxisDirection.unitSubdividePolyline sourceLeading)
          (joinAtEndpoint
            (AxisDirection.unitSubdividePolyline tangentLeading)
            (AxisDirection.unitSubdividePolyline overlap)) := by
      rw [splitTangentSubdivision]
    _ = joinAtEndpoint
          (joinAtEndpoint
            (AxisDirection.unitSubdividePolyline sourceLeading)
            (AxisDirection.unitSubdividePolyline tangentLeading))
          (AxisDirection.unitSubdividePolyline overlap) :=
      joinAtEndpoint_assoc_of_middle_ne_nil
        (AxisDirection.unitSubdividePolyline_ne_nil
          tangentLeadingNonempty)
    _ = joinAtEndpoint
          (AxisDirection.unitSubdividePolyline adjustedSource)
          (AxisDirection.unitSubdividePolyline overlap) := by
      rw [adjustedSubdivision]
    _ = retainedFallbackCardinalForwardLeadingPoints
            route port length slot distance ++
          retainedTerminalFanCardinalForwardOverlapPath
            center port length slot := by
      rw [Computability.joinAtEndpoint_eq_dropLast_append
        adjustedUnitLast overlapUnitHead]
      rfl

end PeriodicEightOccurrenceSplit
end LeanTrominoes
