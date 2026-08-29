/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFallbackOrdinaryNormalizedDirections
import LeanTrominoes.RetainedAngularFanNormalizedFallbackSuffixRadialSemantics

/-! # Semantic correctness of normalized ordinary fallback queries -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit
namespace NormalizedFallbackSuffixDirectionCompiler

open PeriodicOrthocrossing
open FallbackSuffixDirectionCompiler

/-- A positive unary terminal length makes the scaled ordinary radial
prefix nonempty after the fixed interface cost is removed. -/
theorem scaledOrdinaryRadialLength_positive
    (direction : RetainedTerminalDirection)
    (rawLength : Nat)
    (positive : 0 < rawLength) :
    0 <
      retainedTerminalFanOuterRadialLength
        (scaleRetainedTerminalData
          retainedAngularFanSourceClearanceFactor
          (direction, rawLength)) := by
  rcases direction with _ | _ <;>
    rename_i kind <;>
    cases kind <;>
    simp [retainedTerminalFanOuterRadialLength,
      scaleRetainedTerminalData,
      retainedAngularFanSourceClearanceFactor,
      retainedTerminalFanTotalRefinement,
      PeriodicEightOccurrenceSplitPositioned.refinementScale,
      retainedTerminalFanRoutingRefinement,
      retainedTerminalInterfaceMultiplier] <;>
    omega

/-- The normalized suffix compiler's explicit ordinary word is exactly the
canonical normalized direction word of the scaled declarative suffix. -/
theorem compiledDirections_eq_ordinary_normalizedSuffix
    (direction : RetainedTerminalDirection)
    (rawLength : Nat)
    (slot : RetainedTerminalSlot)
    (positive : 0 < rawLength) :
    compiledDirections .ordinary direction rawLength slot =
      retainedNormalizedFallbackFanSuffixDirections
        .ordinary
        (scaleRetainedTerminalData
          retainedAngularFanSourceClearanceFactor
          (direction, rawLength))
        slot := by
  let terminal :=
    scaleRetainedTerminalData
      retainedAngularFanSourceClearanceFactor
      (direction, rawLength)
  have terminalLengthPositive : 0 < terminal.2 :=
    scaleRetainedTerminalData_length_pos
      retainedAngularFanSourceClearanceFactor_pos positive
  have radialPositive :
      0 < retainedTerminalFanOuterRadialLength terminal := by
    simpa [terminal] using
      scaledOrdinaryRadialLength_positive
        direction rawLength positive
  have declarative :=
    retainedFallbackFanOrdinarySuffixRouteAt_normalized_directions_eq
      (0, 0) terminal slot terminalLengthPositive radialPositive
  unfold retainedNormalizedFallbackFanSuffixDirections
  rw [declarative]
  unfold compiledDirections
  rw [exteriorRadialDirections_eq_scaled
    .ordinary direction rawLength positive]
  simp [terminal, List.append_assoc]

end NormalizedFallbackSuffixDirectionCompiler
end PeriodicEightOccurrenceSplit
end LeanTrominoes
