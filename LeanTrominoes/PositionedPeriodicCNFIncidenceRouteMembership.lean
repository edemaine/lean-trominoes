/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PositionedPeriodicCNFIncidenceRouteLookup

/-! # Pointwise incidence-route membership -/

namespace LeanTrominoes
namespace PositionedPeriodicCNF

/-- A genuine positioned-CNF incidence route occurs in the flat edge-route
list of its assembled periodic drawing. -/
theorem incidenceRoute_mem_edgeRoutes
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : IncidenceRoutes)
    {clause : PositionedPeriodicClause Variable}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ source.clauses.zipIdx)
    {literal : PeriodicLiteral Variable}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    routes clauseIndex literalIndex ∈
      (incidenceDrawing source placement routes).edgeRoutes := by
  change
    routes clauseIndex literalIndex ∈
      incidenceEdgeRoutes source routes
  unfold incidenceEdgeRoutes
  apply List.mem_flatMap.mpr
  refine ⟨(clause, clauseIndex), clauseMember, ?_⟩
  exact List.mem_map.mpr
    ⟨(literal, literalIndex), literalMember, rfl⟩

end PositionedPeriodicCNF
end LeanTrominoes
