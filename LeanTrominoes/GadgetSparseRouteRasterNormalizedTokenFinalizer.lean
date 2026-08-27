/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerTime
import LeanTrominoes.GadgetSparseRouteRasterNormalizedTokenData

/-! # Finite finalizer for normalized raster directions -/

noncomputable section

namespace LeanTrominoes
namespace GadgetSparseRouteRasterNormalizedTokens
namespace DirectionFinalizer

open Computability Turing

def transition (_ : Unit) (direction : AxisDirection) :
    Unit × List Token :=
  ((), [.direction direction])

def finish (_ : Unit) : List Token := [.routeEnd]

def output (directions : List AxisDirection) : List Token :=
  FiniteStateTransducer.output () transition finish directions

@[simp] theorem scan (directions : List AxisDirection) :
    FiniteStateTransducer.scan transition () directions =
      ((), directions.map Token.direction) := by
  induction directions with
  | nil => rfl
  | cons direction directions induction =>
      simp [FiniteStateTransducer.scan, transition, induction]

@[simp] theorem output_eq (directions : List AxisDirection) :
    output directions = directionOutput directions := by
  simp [output, directionOutput, FiniteStateTransducer.output, finish]

noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime id id output := by
  change TM2ComputableInPolyTime id id
    (FiniteStateTransducer.output () transition finish)
  exact FiniteStateTransducer.computableInPolyTime () transition finish

end DirectionFinalizer
end GadgetSparseRouteRasterNormalizedTokens
end LeanTrominoes

end
