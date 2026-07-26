import LeanTrominoes.PeriodicEightOccurrenceSplitPortAssignment

/-!
# Ordered fixed-eight occurrence splitting

This module packages the semantic reduction, structural bounds, and
rotation-order port assignment behind one construction.  Its only
source-specific premise is that every chosen occurrence order fits in the
eight Figure 7 compass slots.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicThreeSATThree

/-- Fixed-eight splitting using the ports induced by a chosen per-variable
rotation order. -/
def orderedFormula
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (order : OccurrenceOrder source) :
    PeriodicCNF (ThreeOccurrenceVariable Variable) :=
  formula source (occurrencePortsOfOrder source order)

/-- The ordered fixed-eight construction preserves satisfiability without
any degree premise. -/
theorem orderedFormula_satisfiable_iff
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (order : OccurrenceOrder source) :
    (orderedFormula source order).Satisfiable ↔
      source.Satisfiable := by
  exact satisfiable_iff source
    (occurrencePortsOfOrder source order)

/-- The ordered construction preserves the locality condition. -/
theorem orderedFormula_isLocal
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (order : OccurrenceOrder source)
    (sourceLocal : source.IsLocal) :
    (orderedFormula source order).IsLocal := by
  exact formula_isLocal
    (occurrencePortsOfOrder source order) sourceLocal

/-- The ordered construction preserves width three. -/
theorem orderedFormula_widthAtMostThree
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (order : OccurrenceOrder source)
    (sourceWidth : source.WidthAtMost 3) :
    (orderedFormula source order).WidthAtMost 3 := by
  exact formula_widthAtMostThree
    (occurrencePortsOfOrder source order) sourceWidth

/-- A fitting occurrence order induces the collision-free assignment used
by the occurrence count. -/
theorem orderedFormula_ports_collisionFree
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (order : OccurrenceOrder source)
    (fits : FitsEightSlots order) :
    (occurrencePortsOfOrder source order).CollisionFree
      source :=
  occurrencePortsOfOrder_collisionFree source order fits

/-- If every chosen occurrence list has length at most eight, every output
copy occurs at most three times. -/
theorem orderedFormula_occurrencesAtMostThree
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (order : OccurrenceOrder source)
    (fits : FitsEightSlots order) :
    (orderedFormula source order).OccurrencesAtMost 3 := by
  exact formula_occurrencesAtMostThree source
    (occurrencePortsOfOrder source order)
    (orderedFormula_ports_collisionFree source order fits)

/-- The standard source occurrence predicate supplies the eight-slot
premise for every rotation order. -/
theorem orderedFormula_occurrencesAtMostThree_of_source
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (order : OccurrenceOrder source)
    (sourceOccurrences : source.OccurrencesAtMost 8) :
    (orderedFormula source order).OccurrencesAtMost 3 := by
  exact orderedFormula_occurrencesAtMostThree
    source order
    (fitsEightSlots_of_occurrencesAtMostEight
      order sourceOccurrences)

end PeriodicEightOccurrenceSplit
end LeanTrominoes
