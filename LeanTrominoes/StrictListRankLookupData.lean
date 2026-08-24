/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.StrictListRanks

/-! # Unsorted lookup by strict lower-coordinate rank -/

namespace LeanTrominoes.StrictListRanks

variable {Value Coordinate : Type*} [LinearOrder Coordinate]

/-- Find the first presented value whose number of lower-coordinate values
is `rank`.  Strict coordinate injectivity will make this value unique. -/
def valueAtLowerRank? (coordinate : Value → Coordinate)
    (values : List Value) (rank : Nat) : Option Value :=
  values.find? fun value => lowerRank coordinate values value = rank

end LeanTrominoes.StrictListRanks
