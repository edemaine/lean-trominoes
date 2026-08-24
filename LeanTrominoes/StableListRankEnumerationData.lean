/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Data.Prod.Lex
import LeanTrominoes.StrictListRankEnumerationData

/-! # Stable lower-rank enumeration of finite lists -/

namespace LeanTrominoes.StableListRanks

variable {Value Coordinate : Type*} [LinearOrder Coordinate]

/-- A presented value's coordinate, with its presentation index as the
tie-breaker. -/
def indexedCoordinate (coordinate : Value → Coordinate)
    (entry : Value × Nat) : Coordinate ×ₗ Nat :=
  toLex (coordinate entry.1, entry.2)

/-- Enumerate values by lower coordinate, retaining presentation order among
coordinate ties.  The explicit indices make every rank unique. -/
def valuesByStableLowerRank (coordinate : Value → Coordinate)
    (values : List Value) : List Value :=
  (StrictListRanks.valuesByLowerRank
    (indexedCoordinate coordinate) values.zipIdx).map Prod.fst

end LeanTrominoes.StableListRanks
