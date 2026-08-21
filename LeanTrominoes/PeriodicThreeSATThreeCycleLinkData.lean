/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThree

/-! # Directed occurrence-cycle links -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

/-- Directed links from `current` through `rest`, finally closing to `first`. -/
def cycleLinksFrom {Variable : Type*}
    (first : ThreeOccurrenceVariable Variable) :
    ThreeOccurrenceVariable Variable →
      List (ThreeOccurrenceVariable Variable) →
        List (ThreeOccurrenceVariable Variable ×
          ThreeOccurrenceVariable Variable)
  | current, [] => [(current, first)]
  | current, next :: rest =>
      (current, next) :: cycleLinksFrom first next rest

/-- The directed cycle link stream for one occurrence-copy group. -/
def cycleLinks {Variable : Type*} :
    List (ThreeOccurrenceVariable Variable) →
      List (ThreeOccurrenceVariable Variable ×
        ThreeOccurrenceVariable Variable)
  | [] => []
  | first :: rest => cycleLinksFrom first first rest

/-- All occurrence-cycle links, grouped in source variable order. -/
def allCycleLinks {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    List (ThreeOccurrenceVariable Variable ×
      ThreeOccurrenceVariable Variable) :=
  (sourceVariables source).flatMap fun atom =>
    cycleLinks (occurrenceVariables source atom)

end PeriodicThreeSATThree
end LeanTrominoes
