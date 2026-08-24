/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkData

/-! # Endpoint words of occurrence-cycle links -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree
namespace CycleLinkGroupedPortRanks

/-- Alternating source and target endpoints of a link stream. -/
def linkAtoms {Value : Type*} : List (Value × Value) → List Value
  | [] => []
  | link :: links => link.1 :: link.2 :: linkAtoms links

/-- Alternating endpoints of one occurrence cycle. -/
def cycleLinkAtoms {Variable : Type*}
    (values : List (ThreeOccurrenceVariable Variable)) :
    List (ThreeOccurrenceVariable Variable) :=
  linkAtoms (cycleLinks values)

end CycleLinkGroupedPortRanks
end PeriodicThreeSATThree
end LeanTrominoes
