/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFallbackSuffixDirectionSemantics
import LeanTrominoes.RetainedAngularFanNormalizedFallbackSuffixDirectionCompiler

/-! # Dynamic radial semantics of normalized fallback suffixes -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit
namespace NormalizedFallbackSuffixDirectionCompiler

open PeriodicOrthocrossing
open FallbackSuffixDirectionCompiler

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

private theorem exteriorRadialCount_add_eq
    (kind : RetainedFallbackFanKind)
    (direction : RetainedTerminalDirection)
    (length : Nat) :
    firstRadialCount kind direction - 1 + length * 1152 =
      (retainedTerminalFanOuterRadialLength
          (scaleRetainedTerminalData retainedAngularFanSourceClearanceFactor
            (direction, length + 1)) -
        match kind with
        | .ordinary => 0
        | .escaped => retainedTerminalFanOuterSourceEscapeLength) - 1 := by
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

/-- The unary raw length expands to the scaled terminal's dynamic radial
word with exactly its final primitive block removed. -/
theorem exteriorRadialDirections_eq_scaled
    (kind : RetainedFallbackFanKind)
    (direction : RetainedTerminalDirection)
    (rawLength : Nat)
    (lengthPositive : 0 < rawLength) :
    exteriorRadialDirections kind direction rawLength =
      radialCopies
        ((retainedTerminalFanOuterRadialLength
            (scaleRetainedTerminalData
              retainedAngularFanSourceClearanceFactor
              (direction, rawLength)) -
          match kind with
          | .ordinary => 0
          | .escaped => retainedTerminalFanOuterSourceEscapeLength) - 1)
        direction := by
  cases rawLength with
  | zero => omega
  | succ length =>
      simp only [exteriorRadialDirections]
      unfold firstExteriorRadialDirections
      rw [repeatedFullRadialDirections, ← radialCopies_add]
      congr 1
      simpa [Nat.succ_eq_add_one] using
        exteriorRadialCount_add_eq kind direction length

end NormalizedFallbackSuffixDirectionCompiler
end PeriodicEightOccurrenceSplit
end LeanTrominoes
