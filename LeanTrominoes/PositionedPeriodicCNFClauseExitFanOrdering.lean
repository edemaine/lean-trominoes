/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PlanarOneInThreeNoUnitsFigureNineClauseExitFans

/-!
# Ordered positioned clauses as composed exit fans

This file packages one nonempty width-three positioned clause and its route
first directions as the finite composed Figure 9 exit-fan data.  Genuine
directions and strict clockwise-rank increase are exactly the two generic
properties established by clause-direction ordering.
-/

namespace LeanTrominoes
namespace PositionedPeriodicCNF

open PlanarOneInThreeNoUnitsFigureNine

variable {Variable : Type*}

/-- Finite connector data selected by one positioned clause.  Saturation in
the count field makes the definition total; for arities `1` through `3`, its
active count is exactly the clause arity. -/
def clauseExitFanData
    (clause : PositionedPeriodicClause Variable)
    (clauseIndex : Nat)
    (routes : IncidenceRoutes) : ComposedClauseExitFanData where
  countPred :=
    ⟨min (clause.literals.length - 1) 2, by omega⟩
  direction := fun slot =>
    AxisDirection.polylineFirstDirection
      (routes clauseIndex slot.val)

/-- At every genuine source arity, the finite fan activates exactly the
displayed clause's literals. -/
theorem clauseExitFanData_count_eq
    (clause : PositionedPeriodicClause Variable)
    (clauseIndex : Nat)
    (routes : IncidenceRoutes)
    (positive : 0 < clause.literals.length)
    (width : clause.literals.length ≤ 3) :
    (clauseExitFanData clause clauseIndex routes).count =
      clause.literals.length := by
  simp [clauseExitFanData,
    ComposedClauseExitFanData.count]
  omega

/-- Genuine strictly rank-ordered clause routes select one of the fourteen
verified composed exit fans. -/
theorem clauseExitFanData_valid
    {source : PositionedPeriodicCNF Variable}
    {routes : IncidenceRoutes}
    (directionsGenuine :
      ClauseRouteDirectionsGenuine source routes)
    (ranksIncrease :
      ClauseRouteDirectionRanksStrictlyIncrease source routes)
    {clause : PositionedPeriodicClause Variable}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ source.clauses.zipIdx)
    (positive : 0 < clause.literals.length)
    (width : clause.literals.length ≤ 3) :
    (clauseExitFanData clause clauseIndex routes).IsValid := by
  have countEq := clauseExitFanData_count_eq
    clause clauseIndex routes positive width
  constructor
  · intro slot active
    have slotLt : slot.val < clause.literals.length := by
      rw [← countEq]
      exact active
    let literal := clause.literals.get ⟨slot.val, slotLt⟩
    have literalMember :
        (literal, slot.val) ∈ clause.literals.zipIdx := by
      rw [List.mem_zipIdx_iff_getElem?,
        List.getElem?_eq_some_iff]
      exact ⟨slotLt, rfl⟩
    exact directionsGenuine clause clauseIndex clauseMember
      literal slot.val literalMember
  · intro first second firstActive secondActive firstLtSecond
    have firstLt : first.val < clause.literals.length := by
      rw [← countEq]
      exact firstActive
    have secondLt : second.val < clause.literals.length := by
      rw [← countEq]
      exact secondActive
    exact ranksIncrease clause clauseIndex clauseMember
      ⟨first.val, firstLt⟩ ⟨second.val, secondLt⟩ firstLtSecond

end PositionedPeriodicCNF
end LeanTrominoes
