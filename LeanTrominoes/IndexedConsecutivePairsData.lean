/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingPlanarWires

/-! # Adjacent list pairs from indexed optional lookups -/

namespace LeanTrominoes.IndexedConsecutivePairs

/-- The adjacent pair beginning at `index`, when both optional lookups
succeed. -/
def pairAt? {Value : Type*} (values : List Value) (index : Nat) :
    Option (Value × Value) := do
  let first ← values[index]?
  let second ← values[index + 1]?
  return (first, second)

/-- Enumerate every successful adjacent pair by its zero-based first index. -/
def pairs {Value : Type*} (values : List Value) : List (Value × Value) :=
  (List.range values.length).filterMap (pairAt? values)

end LeanTrominoes.IndexedConsecutivePairs
