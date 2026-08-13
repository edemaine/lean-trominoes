/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PartrecUnpair
import LeanTrominoes.Periodic

/-!
# Explicit decoding of periodic-strip presentations

The standard `Primcodable` representation of a `PeriodicStrip` is the nested
pair

`(width, (period, motifCode))`.

This module begins the direct decoder used by the fitted strip predicates.
The header decoder keeps the motif encoded while exposing the two natural
parameters as native evaluator-list fields.
-/

namespace LeanTrominoes

namespace PeriodicStrip

@[simp]
theorem encode_eq_pair (periodicStrip : PeriodicStrip) :
    Encodable.encode periodicStrip =
      Nat.pair periodicStrip.width
        (Nat.pair periodicStrip.period
          (Encodable.encode periodicStrip.motif)) := by
  rfl

end PeriodicStrip

end LeanTrominoes

namespace Turing.ToPartrec.Code

open LeanTrominoes

/-- Preserve the decoded width while unpairing the rest of the strip header. -/
def periodicStripHeaderRestCode : Code :=
  prepend (get 0) (unpairCode.comp (get 1))

@[simp]
theorem periodicStripHeaderRestCode_eval
    (width period motifCode : Nat) :
    periodicStripHeaderRestCode.eval
        [width, Nat.pair period motifCode] =
      pure [width, period, motifCode] := by
  simp [periodicStripHeaderRestCode]

/-- Decode a standard `PeriodicStrip` code to `[width, period, motifCode]`. -/
def periodicStripHeaderCode : Code :=
  periodicStripHeaderRestCode.comp unpairCode

@[simp]
theorem periodicStripHeaderCode_eval
    (periodicStrip : PeriodicStrip) :
    periodicStripHeaderCode.eval
        [Encodable.encode periodicStrip] =
      pure
        [periodicStrip.width, periodicStrip.period,
          Encodable.encode periodicStrip.motif] := by
  simp [periodicStripHeaderCode]

end Turing.ToPartrec.Code
