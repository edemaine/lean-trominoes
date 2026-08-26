/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicEightOccurrenceSplitCycleBlockIndex
import LeanTrominoes.RetainedAngularFanCompleteRoutes

/-! # Clause-side directions of retained angular-fan cycle routes -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree

/-- Source scaling, local positioning, and the fixed routing refinement leave
the first direction of every appended implication-cycle route unchanged. -/
theorem retainedAngularFanSplicedIncidenceRoutes_cycleBlockStart_firstDirection
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (atom : Variable)
    (atomMember : atom ∈ sourceVariables source.erase)
    (localClauseIndex literalIndex : Nat)
    (localIndex :
      localClauseIndex <
        (PeriodicEightOccurrenceSplit.cycleClausesFor atom).length) :
    AxisDirection.polylineFirstDirection
        (retainedAngularFanSplicedIncidenceRoutes
          source placement routes
          ((PeriodicEightOccurrenceSplitPositioned.occurrenceClauses source
              (occurrencePortsOfAngularOrder source.erase
                (angularOccurrenceOrder source.erase routes))).length +
            (cycleBlockStart (sourceVariables source.erase) atom +
              localClauseIndex))
          literalIndex) =
      AxisDirection.polylineFirstDirection
        (OccurrenceSplitRing.cycleRoutes
          localClauseIndex literalIndex) := by
  rw [retainedAngularFanSplicedIncidenceRoutes_cycle]
  rw [AxisDirection.polylineFirstDirection_scalePolyline
    retainedTerminalFanRoutingRefinement (by
      norm_num [retainedTerminalFanRoutingRefinement])]
  exact allCycleRoutes_cycleBlockStart_firstDirection
    source placement atom atomMember
    localClauseIndex literalIndex localIndex

end PeriodicEightOccurrenceSplit
end LeanTrominoes
