/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFallbackSuffixDirectionCompilerData

/-! # Compiler for retained fallback-fan suffix directions -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit
namespace FallbackSuffixDirectionCompiler

open Computability Turing FiniteStateTransducer
open PeriodicThreeDM.NormalizationDirectionRequest.Batch

private theorem scan_seen
    (kind : RetainedFallbackFanKind)
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot) :
    ∀ length : Nat,
      scan transition ⟨kind, direction, slot, true, true⟩
          (List.replicate length Token.radialUnit ++ [.queryEnd]) =
        (initial,
          (List.replicate length
              (directionTokens (fullRadialDirections direction))).flatten ++
            directionTokens (tailDirections direction slot) ++
              [.routeEnd])
  | 0 => by
      simp [scan, transition, initial]
  | length + 1 => by
      rw [List.replicate_succ, List.cons_append]
      simp only [scan, transition, ↓reduceIte]
      rw [scan_seen kind direction slot length]
      simp [List.replicate_succ, List.append_assoc]

private theorem scan_radial
    (kind : RetainedFallbackFanKind)
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot)
    (length : Nat) :
    scan transition ⟨kind, direction, slot, true, false⟩
        (List.replicate length Token.radialUnit ++ [.queryEnd]) =
      (initial,
        directionTokens (radialDirections kind direction length) ++
          directionTokens (tailDirections direction slot) ++
            [.routeEnd]) := by
  cases length with
  | zero =>
      simp [scan, transition, initial, radialDirections, directionTokens]
  | succ length =>
      rw [List.replicate_succ, List.cons_append]
      simp only [scan, transition, ↓reduceIte]
      change
        ((scan transition ⟨kind, direction, slot, true, true⟩
            (List.replicate length Token.radialUnit ++ [.queryEnd])).1,
          directionTokens (firstRadialDirections kind direction) ++
            (scan transition ⟨kind, direction, slot, true, true⟩
              (List.replicate length Token.radialUnit ++ [.queryEnd])).2) = _
      rw [scan_seen kind direction slot length]
      simp [radialDirections, directionTokens, List.map_append,
        List.append_assoc]

/-- A complete query returns the transducer to its initial control while
emitting exactly one route-delimited compiled suffix. -/
theorem scan_queryTokens
    (kind : RetainedFallbackFanKind)
    (direction : RetainedTerminalDirection)
    (rawLength : Nat)
    (slot : RetainedTerminalSlot) :
    scan transition initial (queryTokens kind direction rawLength slot) =
      (initial,
        directionTokens
            (compiledDirections kind direction rawLength slot) ++
          [.routeEnd]) := by
  unfold queryTokens
  simp only [List.cons_append, scan, transition, List.nil_append]
  rw [scan_radial kind direction slot rawLength]
  simp [compiledDirections, directionTokens,
    List.map_append, List.append_assoc]

/-- A compact kind/direction/slot/unary-length query emits its explicit
route-delimited suffix word. -/
@[simp] theorem output_queryTokens
    (kind : RetainedFallbackFanKind)
    (direction : RetainedTerminalDirection)
    (rawLength : Nat)
    (slot : RetainedTerminalSlot) :
    output (queryTokens kind direction rawLength slot) =
      directionTokens
          (compiledDirections kind direction rawLength slot) ++
        [.routeEnd] := by
  unfold output FiniteStateTransducer.output
  rw [scan_queryTokens]
  simp [finish]

/-- The compact suffix-query interpreter is one fixed finite-state
transducer and hence polynomial-time computable. -/
noncomputable def outputComputableInPolyTime :
    TM2ComputableInPolyTime id id output :=
  FiniteStateTransducer.computableInPolyTime initial transition finish

end FallbackSuffixDirectionCompiler
end PeriodicEightOccurrenceSplit
end LeanTrominoes

end
