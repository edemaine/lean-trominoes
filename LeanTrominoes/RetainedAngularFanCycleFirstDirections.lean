/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicEightOccurrenceSplitCycleBlockIndex
import LeanTrominoes.RetainedAngularFanCompleteRoutes
import LeanTrominoes.RetainedAngularFanSourceScaling

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

/-- The source-first scaling wrapper exposes the same local cycle direction
at the corresponding scaled-source block index. -/
theorem
    retainedAngularFanSourceScaledSplicedIncidenceRoutes_cycleBlockStart_firstDirection
    {Variable : Type*} [DecidableEq Variable]
    (factor : Nat)
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (atom : Variable)
    (atomMember : atom ∈ sourceVariables (source.scale factor).erase)
    (localClauseIndex literalIndex : Nat)
    (localIndex :
      localClauseIndex <
        (PeriodicEightOccurrenceSplit.cycleClausesFor atom).length) :
    AxisDirection.polylineFirstDirection
        (retainedAngularFanSourceScaledSplicedIncidenceRoutes
          factor source placement routes
          ((PeriodicEightOccurrenceSplitPositioned.occurrenceClauses
              (source.scale factor)
              (occurrencePortsOfAngularOrder (source.scale factor).erase
                (angularOccurrenceOrder (source.scale factor).erase
                  (PositionedPeriodicCNF.scaleIncidenceRoutes
                    factor routes)))).length +
            (cycleBlockStart
              (sourceVariables (source.scale factor).erase) atom +
              localClauseIndex))
          literalIndex) =
      AxisDirection.polylineFirstDirection
        (OccurrenceSplitRing.cycleRoutes
          localClauseIndex literalIndex) := by
  exact
    retainedAngularFanSplicedIncidenceRoutes_cycleBlockStart_firstDirection
      (source.scale factor) (placement.scale factor)
      (PositionedPeriodicCNF.scaleIncidenceRoutes factor routes)
      atom atomMember localClauseIndex literalIndex localIndex

end PeriodicEightOccurrenceSplit
end LeanTrominoes
