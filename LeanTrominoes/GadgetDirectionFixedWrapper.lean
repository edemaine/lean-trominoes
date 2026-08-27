/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerData
import LeanTrominoes.OrthogonalPolylineRibbon

/-! # Wrapping a direction stream in fixed finite words -/

namespace LeanTrominoes
namespace Gadget
namespace DirectionFixedWrapper

inductive State
  | start
  | emittedPrefix
  deriving DecidableEq, Fintype

def transition (leading : List AxisDirection) :
    State → AxisDirection → State × List AxisDirection
  | .start, direction => (.emittedPrefix, leading ++ [direction])
  | .emittedPrefix, direction => (.emittedPrefix, [direction])

def finish (leading trailing : List AxisDirection) :
    State → List AxisDirection
  | .start => leading ++ trailing
  | .emittedPrefix => trailing

def output (leading trailing directions : List AxisDirection) :
    List AxisDirection :=
  FiniteStateTransducer.output .start (transition leading)
    (finish leading trailing) directions

@[simp]
theorem scan_emittedPrefix (leading directions : List AxisDirection) :
    FiniteStateTransducer.scan (transition leading) .emittedPrefix
        directions =
      (.emittedPrefix, directions) := by
  induction directions with
  | nil => rfl
  | cons direction directions induction =>
      simp [FiniteStateTransducer.scan, transition, induction]

theorem output_eq (leading trailing directions : List AxisDirection) :
    output leading trailing directions =
      leading ++ directions ++ trailing := by
  cases directions with
  | nil => simp [output, FiniteStateTransducer.output,
      FiniteStateTransducer.scan, finish]
  | cons direction directions =>
      simp [output, FiniteStateTransducer.output,
        FiniteStateTransducer.scan, transition, finish,
        List.append_assoc]

end DirectionFixedWrapper
end Gadget
end LeanTrominoes
