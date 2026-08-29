/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerTime
import LeanTrominoes.RetainedAngularFanFallbackNormalizedTerminalTailData
import LeanTrominoes.RetainedAngularFanFallbackSuffixDirectionCompilerData

/-! # Compact normalized fallback-suffix direction queries -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit
namespace NormalizedFallbackSuffixDirectionCompiler

open PeriodicOrthocrossing
open FallbackSuffixDirectionCompiler

abbrev OutputToken := FallbackSuffixDirectionCompiler.OutputToken
abbrev Token := FallbackSuffixDirectionCompiler.Token

/-- The first positive raw terminal unit emits every dynamic primitive block
except the final one, which belongs to the finite normalized terminal tail. -/
def firstExteriorRadialDirections
    (kind : RetainedFallbackFanKind)
    (direction : RetainedTerminalDirection) : List AxisDirection :=
  radialCopies (firstRadialCount kind direction - 1) direction

/-- Dynamic exterior radial word of a positive raw terminal length. -/
def exteriorRadialDirections
    (kind : RetainedFallbackFanKind)
    (direction : RetainedTerminalDirection) : Nat → List AxisDirection
  | 0 => []
  | length + 1 =>
      firstExteriorRadialDirections kind direction ++
        (List.replicate length
          (fullRadialDirections direction)).flatten

/-- Compiler-side normalized suffix word.  All unbounded repetition stays
in the exterior radial prefix; the final primitive and finite fan geometry
come from one fixed normalized table. -/
def compiledDirections
    (kind : RetainedFallbackFanKind)
    (direction : RetainedTerminalDirection)
    (rawLength : Nat)
    (slot : RetainedTerminalSlot) : List AxisDirection :=
  prefixDirections kind direction slot ++
    exteriorRadialDirections kind direction rawLength ++
      retainedFallbackFanNormalizedTerminalTailDirections direction slot

def queryTokens
    (kind : RetainedFallbackFanKind)
    (direction : RetainedTerminalDirection)
    (rawLength : Nat)
    (slot : RetainedTerminalSlot) : List Token :=
  FallbackSuffixDirectionCompiler.queryTokens
    kind direction rawLength slot

structure Control where
  kind : RetainedFallbackFanKind
  direction : RetainedTerminalDirection
  slot : RetainedTerminalSlot
  ready : Bool
  seenUnit : Bool
  deriving DecidableEq, Fintype

instance : Inhabited Control :=
  ⟨⟨default, default, default, false, false⟩⟩

def initial : Control :=
  ⟨default, default, default, false, false⟩

def transition (control : Control) : Token → Control × List OutputToken
  | .kind kind =>
      (⟨kind, control.direction, control.slot, false, false⟩, [])
  | .terminalDirection direction =>
      (⟨control.kind, direction, control.slot, false, false⟩, [])
  | .slot slot =>
      (⟨control.kind, control.direction, slot, true, false⟩,
        directionTokens
          (prefixDirections control.kind control.direction slot))
  | .radialUnit =>
      if control.ready then
        (⟨control.kind, control.direction, control.slot, true, true⟩,
          directionTokens
            (if control.seenUnit then
              fullRadialDirections control.direction
            else
              firstExteriorRadialDirections
                control.kind control.direction))
      else
        (control, [])
  | .queryEnd =>
      if control.ready then
        (initial,
          directionTokens
              (retainedFallbackFanNormalizedTerminalTailDirections
                control.direction control.slot) ++
            [.routeEnd])
      else
        (initial, [.routeEnd])

def finish (_ : Control) : List OutputToken := []

def output (tokens : List Token) : List OutputToken :=
  FiniteStateTransducer.output initial transition finish tokens

end NormalizedFallbackSuffixDirectionCompiler
end PeriodicEightOccurrenceSplit
end LeanTrominoes
