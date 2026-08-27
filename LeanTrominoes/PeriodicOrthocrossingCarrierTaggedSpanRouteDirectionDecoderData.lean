/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierSpanRouteDirectionDecoderData
import LeanTrominoes.SeparatedBooleanGuardCompiler

/-! # Parity-tagged retained carrier-span decoding data -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierTaggedSpanRouteDirections

open CarrierSpanRouteDirections

inductive ReductionControl
  | zero
  | odd
  | even
  deriving DecidableEq, Fintype, Inhabited

/-- Consume tagged units in pairs and add one final unit to every positive
field.  Both `2s+2` and `2s+3` thereby become the decoder field `s+2`. -/
def reducedTransition : ReductionControl → SourceSymbol →
    ReductionControl × List SourceSymbol
  | .zero, .unit => (.odd, [])
  | .odd, .unit => (.even, [.unit])
  | .even, .unit => (.odd, [])
  | .zero, .delimiter => (.zero, [.delimiter])
  | .odd, .delimiter => (.odd, [.unit, .delimiter])
  | .even, .delimiter => (.even, [.unit, .delimiter])

def reducedFinish (_ : ReductionControl) : List SourceSymbol := []

def reducedOutput (block : List SourceSymbol) : List SourceSymbol :=
  FiniteStateTransducer.output .zero
    reducedTransition reducedFinish block

inductive AxisControl
  | even
  | odd
  | done
  deriving DecidableEq, Fintype, Inhabited

def axisTransition : AxisControl → SourceSymbol →
    AxisControl × List Bool
  | .even, .unit => (.odd, [])
  | .odd, .unit => (.even, [])
  | .even, .delimiter => (.done, [false])
  | .odd, .delimiter => (.done, [true])
  | .done, _ => (.done, [])

def axisFinish : AxisControl → List Bool
  | .even => [false]
  | .odd => [true]
  | .done => []

def axisOutput (block : List SourceSymbol) : List Bool :=
  FiniteStateTransducer.output .even
    axisTransition axisFinish block

def isHorizontal (block : List SourceSymbol) : Bool :=
  (axisOutput block).headD false

def horizontalCandidate (block : List SourceSymbol) : List Token :=
  CarrierSpanRouteDirections.blockOutput true (reducedOutput block)

def verticalCandidate (block : List SourceSymbol) : List Token :=
  CarrierSpanRouteDirections.blockOutput false (reducedOutput block)

/-- Select exactly one orientation from the parity tag.  A zero field selects
the vertical candidate, which is itself empty. -/
def blockOutput (block : List SourceSymbol) : List Token :=
  SeparatedBooleanGuard.guarded
      (isHorizontal block, horizontalCandidate block) ++
    SeparatedBooleanGuard.guarded
      (!isHorizontal block, verticalCandidate block)

def stream (source : List SourceSymbol) : List Token :=
  TM2EndDelimitedBlockMap.mappedOutput
    CarrierSpanRouteDirections.isFieldEnd blockOutput source

end CarrierTaggedSpanRouteDirections
end LeanTrominoes.PeriodicOrthocrossing
