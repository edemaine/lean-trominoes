/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.CellData
import LeanTrominoes.RetainedTerminalDirections

/-! # Canonical carrier-lens route table -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicOrthocrossing
/-- The east-facing equality-lens route table, or its north-facing
quarter-turn, before placing the lens at its carrier endpoint. -/
def carrierLensRawTemplateRoute
    (horizontal : Bool) (span : Int)
    (localClauseIndex literalIndex : Nat) : List Cell :=
  match horizontal, localClauseIndex, literalIndex with
  | true, 0, 0 => [(3, 0), (0, 0)]
  | true, 0, 1 => [(3, 0), (3, -2), (span, -2), (span, 0)]
  | true, 1, 0 => [(6, 0), (6, 1), (0, 1), (0, 0)]
  | true, 1, 1 => [(6, 0), (span, 0)]
  | false, 0, 0 => [(0, 3), (0, 0)]
  | false, 0, 1 => [(0, 3), (2, 3), (2, span), (0, span)]
  | false, 1, 0 => [(0, 6), (-1, 6), (-1, 0), (0, 0)]
  | false, 1, 1 => [(0, 6), (0, span)]
  | _, _, _ => []

/-- Terminal data parallel to `carrierLensRawTemplateRoute`, kept lightweight
so its finite classifier leaves do not import the full metadata pipeline. -/
def carrierLensTemplateTerminalData
    (horizontal : Bool) (span : Int) :
    Nat → Nat → RetainedTerminalDirection × Nat
  | 0, 0 =>
      (.compass (if horizontal then .east else .south), 3)
  | 0, 1 =>
      (.compass (if horizontal then .north else .east), 2)
  | 1, 0 =>
      (.compass (if horizontal then .south else .west), 1)
  | 1, 1 =>
      (.compass (if horizontal then .west else .north),
        (span - 6).toNat)
  | _, _ => (.compass .east, 1)

end PeriodicEightOccurrenceSplit
end LeanTrominoes
