/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularOccurrenceGlobalStableRankStream

/-! # Count data for global retained occurrence stable ranks -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicThreeSATThree

variable {Variable : Type*} [DecidableEq Variable]

/-- Whether a candidate belongs to the target atom and has a strictly lower
terminal coordinate. -/
def retainedOccurrenceGlobalStableLowerPredicate
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (target candidate : ThreeOccurrenceVariable Variable) : Bool :=
  decide (candidate.1 = target.1) &&
    decide
      (retainedOccurrenceTerminalCoordinate routes candidate <
        retainedOccurrenceTerminalCoordinate routes target)

/-- Whether a candidate belongs to the target atom and has the same terminal
coordinate.  Prefix counting retains exactly the earlier presentation ties. -/
def retainedOccurrenceGlobalStableTiePredicate
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (target candidate : ThreeOccurrenceVariable Variable) : Bool :=
  decide (candidate.1 = target.1) &&
    decide
      (retainedOccurrenceTerminalCoordinate routes candidate =
        retainedOccurrenceTerminalCoordinate routes target)

/-- Strict-lower comparison rows in target-major global occurrence order. -/
def retainedOccurrenceGlobalStableLowerRows
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) : List (List Bool) :=
  let copies := allOccurrenceVariables source
  copies.map fun target =>
    copies.map (retainedOccurrenceGlobalStableLowerPredicate routes target)

/-- Equal-coordinate comparison rows in target-major global occurrence
order. -/
def retainedOccurrenceGlobalStableTieRows
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) : List (List Bool) :=
  let copies := allOccurrenceVariables source
  copies.map fun target =>
    copies.map (retainedOccurrenceGlobalStableTiePredicate routes target)

/-- Count implementation of one globally indexed stable rank. -/
def retainedOccurrenceGlobalStableTerminalRankCountAt
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (copies : List (ThreeOccurrenceVariable Variable))
    (entry : ThreeOccurrenceVariable Variable × Nat) : Nat :=
  (copies.map
      (retainedOccurrenceGlobalStableLowerPredicate routes entry.1)).count
      true +
    ((copies.map
      (retainedOccurrenceGlobalStableTiePredicate routes entry.1)).take
      entry.2).count true

/-- Count-computed stable ranks in global occurrence presentation order. -/
def retainedOccurrenceGlobalStableTerminalRankCounts
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) : List Nat :=
  let copies := allOccurrenceVariables source
  copies.zipIdx.map
    (retainedOccurrenceGlobalStableTerminalRankCountAt routes copies)

end PeriodicEightOccurrenceSplit
end LeanTrominoes
