/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetPreparedHeaderSemantics
import LeanTrominoes.TM2CompositionMachine

/-! # Prepared strip headers from a unary period scale

The rectangular normalization used by the strip reduction has horizontal
period `P` and vertical period `3 * P + 1`.  This file gives a fixed finite
machine which starts from one input symbol per unit of an underlying scale
`g`, takes `P = factor * g`, and emits the two prepared header fields in the
order expected by the gadget-pixel compiler.

The exact token algebra is isolated in `GadgetPreparedHeaderData`; this leaf
only composes its three unary-padding passes and final block transducer.
-/

noncomputable section

namespace LeanTrominoes
namespace GadgetPreparedHeaderEmitter

open Computability Turing
def addSentinelComputableInPolyTime :
    TM2ComputableInPolyTime id id addSentinel :=
  UnaryPolynomialPaddingMachine.computableInPolyTime selectNone [1]

def addPeriodComputableInPolyTime (factor : Nat) :
    TM2ComputableInPolyTime id id (addPeriod factor) :=
  UnaryPolynomialPaddingMachine.computableInPolyTime selectGrid [0, factor]

def addEndComputableInPolyTime :
    TM2ComputableInPolyTime id id addEnd :=
  UnaryPolynomialPaddingMachine.computableInPolyTime selectNone [1]

def blockComputableInPolyTime (factor : Nat) :
    TM2ComputableInPolyTime id id
      (fun word : List EndSymbol => word.flatMap (block factor)) :=
  FiniteBlockTransducer.computableInPolyTime (block factor)

/-- The prepared rectangular header is computable in polynomial time from
the unary underlying scale. -/
def computableInPolyTime (factor : Nat) :
    TM2ComputableInPolyTime id id (preparedHeader factor) := by
  let sentinel := addSentinelComputableInPolyTime
  let period := TM2CompositionMachine.computableInPolyTime sentinel
    (addPeriodComputableInPolyTime factor)
  let ending := TM2CompositionMachine.computableInPolyTime period
    addEndComputableInPolyTime
  let emitted := TM2CompositionMachine.computableInPolyTime ending
    (blockComputableInPolyTime factor)
  exact emitted

end GadgetPreparedHeaderEmitter
end LeanTrominoes
