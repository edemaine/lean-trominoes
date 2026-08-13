/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCoordinatedRouteValidity

/-!
# Strict source-escape room in the final retained drawing

The final source-clearance scaling is large enough that the fixed escaped
prefix leaves a nonempty radial suffix for every classified retained
terminal.  This strengthens the earlier non-strict endpoint-validity bound
for the separation arguments that use the suffix itself.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

/-- Scaling a positive retained terminal by four leaves strictly more than
the fixed source-escape length before the outer interface. -/
theorem retainedTerminalFanOuterSourceEscape_strictlyFits_scale_four
    (terminal : RetainedTerminalData)
    (lengthPositive : 0 < terminal.2) :
    retainedTerminalFanOuterSourceEscapeLength <
      retainedTerminalFanOuterRadialLength
        (scaleRetainedTerminalData 4 terminal) := by
  rcases terminal with ⟨direction, length⟩
  cases direction with
  | compass port =>
      cases port <;>
        simp [scaleRetainedTerminalData,
          retainedTerminalFanOuterSourceEscapeLength,
          retainedTerminalFanOuterRadialLength,
          retainedTerminalFanTotalRefinement,
          PeriodicEightOccurrenceSplitPositioned.refinementScale,
          retainedTerminalFanRoutingRefinement,
          retainedTerminalInterfaceMultiplier] at lengthPositive ⊢ <;>
        omega
  | routedClause arm =>
      cases arm <;>
        simp [scaleRetainedTerminalData,
          retainedTerminalFanOuterSourceEscapeLength,
          retainedTerminalFanOuterRadialLength,
          retainedTerminalFanTotalRefinement,
          PeriodicEightOccurrenceSplitPositioned.refinementScale,
          retainedTerminalFanRoutingRefinement,
          retainedTerminalInterfaceMultiplier] at lengthPositive ⊢ <;>
        omega

end PeriodicEightOccurrenceSplit

namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicThreeSATThree

/-- Every classified terminal of a genuine final incidence retains a
nonempty radial suffix after its delayed-lane escape. -/
theorem finalCoordinatedScaledSourceRoute_escapeStrict
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    let rawRoute :=
      finalCoordinatedSourceRoutes formula clauseIndex literalIndex
    let rawTerminal :=
      classifiedRetainedTerminalData
        (routeTerminalVector rawRoute)
    retainedTerminalFanOuterSourceEscapeLength <
      retainedTerminalFanOuterRadialLength
        (scaleRetainedTerminalData
          retainedAngularFanSourceClearanceFactor rawTerminal) := by
  dsimp only
  rw [show retainedAngularFanSourceClearanceFactor = 4 by rfl]
  exact
    retainedTerminalFanOuterSourceEscape_strictlyFits_scale_four
      (classifiedRetainedTerminalData
        (routeTerminalVector
          (finalCoordinatedSourceRoutes
            formula clauseIndex literalIndex)))
      (finalCoordinatedSourceRoute_terminal_length_positive
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember)

end PeriodicOrthocrossing
end LeanTrominoes
