/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalDirectClauseTerminalColumn

/-! # Semantics of terminal columns carried by direct-clause queries -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicOrthocrossing

/-- On a successful direct-atlas lookup, the coordinate carried by the
finite copied-source query is the actual unscaled coordinated-source
terminal coordinate.  Failed lookups are omitted for the fallback-family
compilers. -/
theorem retainedFinalDirectTerminalCoordinate?_sourceQuery
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clauseIndex literalIndex : Nat)
    (literal :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)) :
    retainedFinalDirectTerminalCoordinate?
        (retainedFinalCopiedSourceDirectionQuery
          formula clauseIndex literalIndex literal) =
      match retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex with
      | none => none
      | some _ =>
          some (ofLex
            (retainedOccurrenceTerminalCoordinate
              (finalCoordinatedSourceRoutes formula)
              (literal.atom, clauseIndex, literalIndex))) := by
  unfold retainedFinalCopiedSourceDirectionQuery
  cases choiceLookup : retainedFinalDirectSourceRouteChoice?
      formula clauseIndex literalIndex with
  | none => rfl
  | some choice =>
      simp only [retainedFinalDirectTerminalCoordinate?]
      exact congrArg (fun coordinate => some (ofLex coordinate))
        (retainedOccurrenceTerminalCoordinate_eq_directChoiceQuery
          formula clauseIndex literalIndex literal choice choiceLookup).symm

end PeriodicEightOccurrenceSplit
end LeanTrominoes

