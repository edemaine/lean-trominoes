/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanBoundaryRouteFamily
import LeanTrominoes.RetainedAngularOccurrenceStableRank

/-! # Bounded stable numeric ranks of retained angular occurrences -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree

/-- On a genuine certified occurrence, bounding its geometric angular index
selects exactly the same Figure 7 slot as bounding its stable numeric
terminal rank. -/
theorem boundedAngularOccurrenceIndex_eq_boundedStableTerminalRank
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (certificate :
      RetainedOccurrenceTerminalCertificate source.erase routes)
    (literal : PeriodicLiteral Variable)
    (clauseIndex literalIndex : Nat)
    (taggedMember :
      (literal, clauseIndex, literalIndex) ∈ taggedLiterals source.erase) :
    boundedRetainedTerminalSlot
        (angularOccurrenceIndex
          (angularOccurrenceOrder source.erase routes)
          literal clauseIndex literalIndex) =
      boundedRetainedTerminalSlot
        (retainedOccurrenceStableTerminalRank
          source.erase routes literal.atom
          (literal.atom, clauseIndex, literalIndex)) := by
  apply congrArg boundedRetainedTerminalSlot
  unfold angularOccurrenceIndex angularOccurrenceOrder indexedOccurrence
  dsimp only
  exact
    angularOccurrenceVariables_idxOf_eq_stableTerminalRank
      source.erase routes certificate literal clauseIndex literalIndex
      taggedMember

end PeriodicEightOccurrenceSplit
end LeanTrominoes
