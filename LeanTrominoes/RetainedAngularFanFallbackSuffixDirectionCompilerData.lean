/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerTime
import LeanTrominoes.RetainedAngularFanFallbackSuffixDirectionData
import LeanTrominoes.PeriodicThreeDMNormalizationDirectionRequestBatchInnerCompiler

/-! # Compact queries for retained fallback-fan suffix directions -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit
namespace FallbackSuffixDirectionCompiler

open PeriodicOrthocrossing

abbrev OutputToken :=
  PeriodicThreeDM.NormalizationDirectionRequest.Batch.NormalizedToken

instance suffixCompilerTerminalDirectionInhabited :
    Inhabited RetainedTerminalDirection :=
  ⟨.compass .east⟩

/-- A fixed header followed by a unary raw terminal length. -/
inductive Token
  | kind (value : RetainedFallbackFanKind)
  | terminalDirection (value : RetainedTerminalDirection)
  | slot (value : RetainedTerminalSlot)
  | radialUnit
  | queryEnd
  deriving DecidableEq, Fintype, Inhabited

def directionTokens (directions : List AxisDirection) : List OutputToken :=
  directions.map .direction

/-- Unit-staircase word for one inward primitive ray step. -/
def inwardRayUnitDirections
    (direction : RetainedTerminalDirection) : List AxisDirection :=
  Gadget.unitSubdivisionDirections
    ((retainedTerminalFanOuterInwardRay (direction, 1)).rasterize (0, 0))

/-- Repeat a primitive inward-ray staircase by a supplied count. -/
def radialCopies
    (count : Nat) (direction : RetainedTerminalDirection) :
    List AxisDirection :=
  (List.replicate count (inwardRayUnitDirections direction)).flatten

/-- Fixed interface length removed from the refined raw terminal ray. -/
def interfaceCost (direction : RetainedTerminalDirection) : Nat :=
  retainedTerminalFanRoutingRefinement *
    retainedTerminalInterfaceMultiplier direction

/-- Radial repeats contributed by the first raw terminal unit.  The escaped
policy also reserves its initial 64 repeats before the lane shift. -/
def firstRadialCount
    (kind : RetainedFallbackFanKind)
    (direction : RetainedTerminalDirection) : Nat :=
  match kind with
  | .ordinary => 1152 - interfaceCost direction
  | .escaped =>
      1152 - interfaceCost direction -
        retainedTerminalFanOuterSourceEscapeLength

def firstRadialDirections
    (kind : RetainedFallbackFanKind)
    (direction : RetainedTerminalDirection) : List AxisDirection :=
  radialCopies (firstRadialCount kind direction) direction

def fullRadialDirections
    (direction : RetainedTerminalDirection) : List AxisDirection :=
  radialCopies 1152 direction

/-- Finite directions emitted once the kind, terminal direction, and slot
header has been read. -/
def prefixDirections
    (kind : RetainedFallbackFanKind)
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot) : List AxisDirection :=
  match kind with
  | .ordinary =>
      Gadget.unitSubdivisionDirections
        (retainedTerminalFanOuterLaneShiftRoute direction slot)
  | .escaped =>
      Gadget.unitSubdivisionDirections
          ((retainedTerminalFanOuterSourceEscapeRay
            (direction, 1)).rasterize (0, 0)) ++
        Gadget.unitSubdivisionDirections
          (retainedTerminalFanOuterLaneShiftRoute direction slot)

/-- Finite local-fan and Figure 7 directions emitted at the query end. -/
def tailDirections
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot) : List AxisDirection :=
  Gadget.unitSubdivisionDirections
      (retainedTerminalFanOuterLocalRouteAt (0, 0) direction slot) ++
    Gadget.unitSubdivisionDirections
      (retainedTerminalFanFigure7SpokeRouteAt (0, 0) slot)

/-- Dynamic radial word represented by one positive raw terminal length. -/
def radialDirections
    (kind : RetainedFallbackFanKind)
    (direction : RetainedTerminalDirection) : Nat → List AxisDirection
  | 0 => []
  | length + 1 =>
      firstRadialDirections kind direction ++
        (List.replicate length
          (fullRadialDirections direction)).flatten

/-- Explicit compiler-side suffix word. -/
def compiledDirections
    (kind : RetainedFallbackFanKind)
    (direction : RetainedTerminalDirection)
    (rawLength : Nat)
    (slot : RetainedTerminalSlot) : List AxisDirection :=
  prefixDirections kind direction slot ++
    radialDirections kind direction rawLength ++
      tailDirections direction slot

def queryTokens
    (kind : RetainedFallbackFanKind)
    (direction : RetainedTerminalDirection)
    (rawLength : Nat)
    (slot : RetainedTerminalSlot) : List Token :=
  [.kind kind, .terminalDirection direction, .slot slot] ++
    List.replicate rawLength .radialUnit ++ [.queryEnd]

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
        directionTokens (prefixDirections control.kind control.direction slot))
  | .radialUnit =>
      if control.ready then
        (⟨control.kind, control.direction, control.slot, true, true⟩,
          directionTokens
            (if control.seenUnit then
              fullRadialDirections control.direction
            else
              firstRadialDirections control.kind control.direction))
      else
        (control, [])
  | .queryEnd =>
      if control.ready then
        (initial,
          directionTokens
              (tailDirections control.direction control.slot) ++
            [.routeEnd])
      else
        (initial, [.routeEnd])

def finish (_ : Control) : List OutputToken := []

def output (tokens : List Token) : List OutputToken :=
  FiniteStateTransducer.output initial transition finish tokens

end FallbackSuffixDirectionCompiler
end PeriodicEightOccurrenceSplit
end LeanTrominoes
