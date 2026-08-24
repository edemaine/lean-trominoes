/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.StrictListRankLookupData

/-! # Natural-range enumeration by strict lower-coordinate rank -/

namespace LeanTrominoes.StrictListRanks

variable {Value Coordinate : Type*} [LinearOrder Coordinate]

/-- Enumerate the presented values in geometric rank order by repeated
unsorted lower-rank lookup. -/
def valuesByLowerRank (coordinate : Value → Coordinate)
    (values : List Value) : List Value :=
  (List.range values.length).filterMap
    (valueAtLowerRank? coordinate values)

end LeanTrominoes.StrictListRanks
