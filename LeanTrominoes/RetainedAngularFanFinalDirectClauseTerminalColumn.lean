/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanDirectSourceTerminalCoordinateQuery
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseQuery

/-! # Terminal columns carried by final direct-clause queries -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

/-- The unscaled terminal coordinate carried by a direct copied-source
query.  Fallback queries are omitted; they belong to the separately compiled
carrier and bend families. -/
def retainedFinalDirectTerminalCoordinate? :
    RetainedFinalCopiedSourceDirectionQuery → Option (Nat × Nat)
  | .direct query =>
      some (ofLex (retainedDirectSourceTerminalCoordinateOfQuery query))
  | .fallback _ => none

/-- Presentation-ordered direct terminal coordinates carried by one finite
copied-clause query.  Precomputed fallback clauses contribute no values. -/
def retainedFinalDirectClauseTerminalCoordinates :
    RetainedFinalCopiedClauseQuery → List (Nat × Nat)
  | .precomputed _ => []
  | .unary _ firstDirection =>
      (retainedFinalDirectTerminalCoordinate? firstDirection).toList
  | .binary _ firstDirection _ secondDirection =>
      (retainedFinalDirectTerminalCoordinate? firstDirection).toList ++
        (retainedFinalDirectTerminalCoordinate? secondDirection).toList
  | .ternary _ firstDirection _ secondDirection _ thirdDirection =>
      (retainedFinalDirectTerminalCoordinate? firstDirection).toList ++
        (retainedFinalDirectTerminalCoordinate? secondDirection).toList ++
          (retainedFinalDirectTerminalCoordinate? thirdDirection).toList

/-- Direct terminal coordinates carried by a complete clause-query stream. -/
def retainedFinalDirectTerminalCoordinates
    (queries : List RetainedFinalCopiedClauseQuery) : List (Nat × Nat) :=
  queries.flatMap retainedFinalDirectClauseTerminalCoordinates

/-- Angular-rank projection of the direct terminal-query stream. -/
def retainedFinalDirectTerminalDirectionRanks
    (queries : List RetainedFinalCopiedClauseQuery) : List Nat :=
  (retainedFinalDirectTerminalCoordinates queries).map Prod.fst

/-- Radial-length projection of the direct terminal-query stream. -/
def retainedFinalDirectTerminalRadialLengths
    (queries : List RetainedFinalCopiedClauseQuery) : List Nat :=
  (retainedFinalDirectTerminalCoordinates queries).map Prod.snd

end PeriodicEightOccurrenceSplit
end LeanTrominoes
