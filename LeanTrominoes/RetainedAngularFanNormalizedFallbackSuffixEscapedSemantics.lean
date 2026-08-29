/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFallbackEscapedNormalizedDirections
import LeanTrominoes.RetainedAngularFanFinalStrictEscape
import LeanTrominoes.RetainedAngularFanNormalizedFallbackSuffixRadialSemantics

/-! # Semantic correctness of normalized escaped fallback queries -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit
namespace NormalizedFallbackSuffixDirectionCompiler

open PeriodicOrthocrossing
open FallbackSuffixDirectionCompiler

/-- The normalized suffix compiler's explicit escaped word is exactly the
canonical normalized direction word of the scaled declarative suffix. -/
theorem compiledDirections_eq_escaped_normalizedSuffix
    (direction : RetainedTerminalDirection)
    (rawLength : Nat)
    (slot : RetainedTerminalSlot)
    (positive : 0 < rawLength) :
    compiledDirections .escaped direction rawLength slot =
      retainedNormalizedFallbackFanSuffixDirections
        .escaped
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
  have escapeStrict :
      retainedTerminalFanOuterSourceEscapeLength <
        retainedTerminalFanOuterRadialLength terminal := by
    change
      retainedTerminalFanOuterSourceEscapeLength <
        retainedTerminalFanOuterRadialLength
          (scaleRetainedTerminalData
            retainedAngularFanSourceClearanceFactor
            (direction, rawLength))
    rw [retainedAngularFanSourceClearanceFactor_eq]
    exact retainedTerminalFanOuterSourceEscape_strictlyFits_scale_four
      (direction, rawLength) positive
  have declarative :=
    retainedFallbackFanEscapedSuffixRouteAt_normalized_directions_eq
      (0, 0) terminal slot terminalLengthPositive escapeStrict
  unfold retainedNormalizedFallbackFanSuffixDirections
  rw [declarative]
  unfold compiledDirections
  rw [exteriorRadialDirections_eq_scaled
    .escaped direction rawLength positive]
  simp [terminal, List.append_assoc]

end NormalizedFallbackSuffixDirectionCompiler
end PeriodicEightOccurrenceSplit
end LeanTrominoes
