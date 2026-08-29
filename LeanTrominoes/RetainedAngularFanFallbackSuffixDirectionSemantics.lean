/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFallbackSuffixOuterDirectionSemantics

/-! # Exact semantics of compiled retained fallback suffix directions -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit
namespace FallbackSuffixDirectionCompiler

open PeriodicOrthocrossing

private theorem radialCopies_add
    (first second : Nat) (direction : RetainedTerminalDirection) :
    radialCopies (first + second) direction =
      radialCopies first direction ++ radialCopies second direction := by
  unfold radialCopies
  rw [List.replicate_add, List.flatten_append]

private theorem repeatedFullRadialDirections
    (count : Nat) (direction : RetainedTerminalDirection) :
    (List.replicate count (fullRadialDirections direction)).flatten =
      radialCopies (count * 1152) direction := by
  induction count with
  | zero => simp [radialCopies]
  | succ count induction =>
      rw [List.replicate_succ, List.flatten_cons, induction]
      unfold fullRadialDirections
      rw [← radialCopies_add]
      congr 1
      omega

private theorem firstRadialCount_add_eq
    (kind : RetainedFallbackFanKind)
    (direction : RetainedTerminalDirection)
    (length : Nat) :
    firstRadialCount kind direction + length * 1152 =
      retainedTerminalFanOuterRadialLength
          (scaleRetainedTerminalData retainedAngularFanSourceClearanceFactor
            (direction, length + 1)) -
        match kind with
        | .ordinary => 0
        | .escaped => retainedTerminalFanOuterSourceEscapeLength := by
  cases kind <;> cases direction with
  | compass port =>
      cases port <;>
        simp [firstRadialCount, interfaceCost,
          retainedTerminalFanOuterRadialLength,
          retainedAngularFanSourceClearanceFactor,
          scaleRetainedTerminalData, retainedTerminalFanTotalRefinement,
          PeriodicEightOccurrenceSplitPositioned.refinementScale,
          retainedTerminalFanRoutingRefinement,
          retainedTerminalInterfaceMultiplier,
          retainedTerminalFanOuterSourceEscapeLength] <;>
        omega
  | routedClause arm =>
      cases arm <;>
        simp [firstRadialCount, interfaceCost,
          retainedTerminalFanOuterRadialLength,
          retainedAngularFanSourceClearanceFactor,
          scaleRetainedTerminalData, retainedTerminalFanTotalRefinement,
          PeriodicEightOccurrenceSplitPositioned.refinementScale,
          retainedTerminalFanRoutingRefinement,
          retainedTerminalInterfaceMultiplier,
          retainedTerminalFanOuterSourceEscapeLength] <;>
        omega

/-- The unary raw length expands to exactly the scaled terminal's dynamic
radial word, with the fixed escape removed only for the escaped policy. -/
theorem radialDirections_eq_scaled
    (kind : RetainedFallbackFanKind)
    (direction : RetainedTerminalDirection)
    (rawLength : Nat)
    (lengthPositive : 0 < rawLength) :
    radialDirections kind direction rawLength =
      radialCopies
        (retainedTerminalFanOuterRadialLength
            (scaleRetainedTerminalData
              retainedAngularFanSourceClearanceFactor
              (direction, rawLength)) -
          match kind with
          | .ordinary => 0
          | .escaped => retainedTerminalFanOuterSourceEscapeLength)
        direction := by
  cases rawLength with
  | zero => omega
  | succ length =>
      simp only [radialDirections]
      unfold firstRadialDirections
      rw [repeatedFullRadialDirections, ← radialCopies_add]
      congr 1
      simpa [Nat.succ_eq_add_one] using
        firstRadialCount_add_eq kind direction length

/-- A compact positive query emits exactly the complete fallback suffix of
the factor-four-scaled retained terminal. -/
theorem compiledDirections_eq_retainedFallbackFanSuffixDirections
    (kind : RetainedFallbackFanKind)
    (direction : RetainedTerminalDirection)
    (rawLength : Nat)
    (slot : RetainedTerminalSlot)
    (lengthPositive : 0 < rawLength) :
    compiledDirections kind direction rawLength slot =
      retainedFallbackFanSuffixDirections kind
        (scaleRetainedTerminalData retainedAngularFanSourceClearanceFactor
          (direction, rawLength)) slot := by
  let scaledTerminal :=
    scaleRetainedTerminalData retainedAngularFanSourceClearanceFactor
      (direction, rawLength)
  have scaledLengthPositive : 0 < scaledTerminal.2 := by
    exact scaleRetainedTerminalData_length_pos
      retainedAngularFanSourceClearanceFactor_pos lengthPositive
  have valid : kind.Valid scaledTerminal := by
    cases kind with
    | ordinary => trivial
    | escaped =>
        change retainedTerminalFanOuterSourceEscapeLength ≤
          retainedTerminalFanOuterRadialLength scaledTerminal
        simpa [scaledTerminal, retainedAngularFanSourceClearanceFactor] using
          retainedTerminalFanOuterSourceEscape_fits_scale_four
            (direction, rawLength) lengthPositive
  rw [retainedFallbackFanSuffixDirections_eq kind scaledTerminal slot
    scaledLengthPositive valid]
  cases kind with
  | ordinary =>
      simp only [RetainedFallbackFanKind.outerRouteAt]
      rw [retainedTerminalFanOuterCompleteRoute_directions
        (0, 0) scaledTerminal slot scaledLengthPositive]
      unfold compiledDirections
      rw [radialDirections_eq_scaled .ordinary direction rawLength
        lengthPositive]
      simp [tailDirections, scaledTerminal,
        List.append_assoc]
  | escaped =>
      simp only [RetainedFallbackFanKind.outerRouteAt]
      rw [retainedTerminalFanOuterEscapedCompleteRoute_directions
        (0, 0) scaledTerminal slot scaledLengthPositive valid]
      unfold compiledDirections
      rw [radialDirections_eq_scaled .escaped direction rawLength
        lengthPositive]
      simp [tailDirections, scaledTerminal,
        List.append_assoc]

end FallbackSuffixDirectionCompiler
end PeriodicEightOccurrenceSplit
end LeanTrominoes
