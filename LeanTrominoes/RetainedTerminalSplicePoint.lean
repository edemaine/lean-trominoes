/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalPolylineTailReplacement
import LeanTrominoes.RetainedAngularTerminalDataProfile

/-!
# Splice points of classified retained terminal segments

A length-aware retained terminal datum describes the last segment backwards
from its variable endpoint.  This file identifies that vector with the
polyline's total `polylineLastEntrance` lookup and therefore turns the
classifier output into an exact geometric splice point.

The later adapter can discard the old final segment—including any
intentional collinear overlap in Figure 8(b)—and attach a replacement suffix
at this certified penultimate source point.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicThreeSATThree

/-- On a genuine route, the backwards terminal vector is the penultimate
point minus the advertised last point. -/
theorem routeTerminalVector_eq_sub_lastEntrance
    (route : List Cell)
    (routeLength : 2 ≤ route.length) :
    routeTerminalVector route =
      Cell.sub
        (polylineLastEntrance route)
        (route.getLastD (0, 0)) := by
  generalize reversedEq : route.reverse = reversed
  cases reversed with
  | nil =>
      have : route = [] := by
        simpa using congrArg List.reverse reversedEq
      subst route
      simp at routeLength
  | cons target rest =>
      cases rest with
      | nil =>
          have : route = [target] := by
            simpa using congrArg List.reverse reversedEq
          subst route
          simp at routeLength
      | cons entrance rest =>
          have routeEq :
              route =
                (target :: entrance :: rest).reverse := by
            simpa using congrArg List.reverse reversedEq
          subst route
          simp [routeTerminalVector,
            polylineLastEntrance, polylineFirstExit]
          rw [show
            rest.reverse ++ [entrance, target] =
              (rest.reverse ++ [entrance]) ++ [target] by
                simp]
          rw [gridPolylineSegments_append_singleton_of_ne_nil
            (rest.reverse ++ [entrance])
            entrance target (by simp)]
          simp

/-- The local radial point represented by a length-aware retained terminal
datum, measured backwards from the variable endpoint. -/
def retainedTerminalSplicePoint
    (target : Cell) (terminal : RetainedTerminalData) : Cell :=
  Cell.add target
    (Cell.scale terminal.2 terminal.1.primitive)

/-- Exact terminal classification locates the penultimate source point at
the datum's radial splice point. -/
theorem polylineLastEntrance_eq_retainedTerminalSplicePoint
    {route : List Cell}
    (routeLength : 2 ≤ route.length)
    {terminal : RetainedTerminalData}
    (classified :
      retainedTerminalDirectionClassify
          (routeTerminalVector route) =
        some terminal) :
    polylineLastEntrance route =
      retainedTerminalSplicePoint
        (route.getLastD (0, 0)) terminal := by
  have sound :=
    retainedTerminalDirectionClassify_sound classified
  rw [routeTerminalVector_eq_sub_lastEntrance
    route routeLength] at sound
  apply Prod.ext
  · have horizontal := congrArg Prod.fst sound.2
    simp [retainedTerminalSplicePoint,
      Cell.add, Cell.sub, Cell.scale] at horizontal ⊢
    omega
  · have vertical := congrArg Prod.snd sound.2
    simp [retainedTerminalSplicePoint,
      Cell.add, Cell.sub, Cell.scale] at vertical ⊢
    omega

/-- The splice point is genuinely different from the discarded variable
endpoint. -/
theorem retainedTerminalSplicePoint_ne
    (target : Cell) (terminal : RetainedTerminalData)
    (lengthPositive : 0 < terminal.2) :
    retainedTerminalSplicePoint target terminal ≠ target := by
  intro equal
  have primitiveNonzero :=
    terminal.1.primitive_ne_zero
  rcases target with ⟨targetX, targetY⟩
  rcases terminal.1.primitive with
    ⟨primitiveX, primitiveY⟩
  simp only [retainedTerminalSplicePoint,
    Cell.add, Cell.scale, Prod.mk.injEq] at equal
  apply primitiveNonzero
  apply Prod.ext
  · simp only
    nlinarith [equal.1]
  · simp only
    nlinarith [equal.2]

end PeriodicEightOccurrenceSplit
end LeanTrominoes
