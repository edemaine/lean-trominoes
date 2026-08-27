/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteUnitSubdivisionDirectionTranslation
import LeanTrominoes.PositionedPeriodicCNFVariableGaugeDrawing

/-! # Direction words through canonical variable gauges -/

namespace LeanTrominoes
namespace PositionedPeriodicCNF

open Gadget

/-- A canonical variable gauge translates the whole selected incidence route
by one common vector, so it preserves the complete direction word. -/
theorem unitSubdivisionDirections_variableGaugeCanonicalIncidenceRoutes_of_clause_mem
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (gauge : Variable → Cell)
    (routes : IncidenceRoutes)
    {clause : PositionedPeriodicClause Variable}
    {clauseIndex literalIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ source.clauses.zipIdx) :
    unitSubdivisionDirections
        (variableGaugeCanonicalIncidenceRoutes source placement gauge routes
          clauseIndex literalIndex) =
      unitSubdivisionDirections (routes clauseIndex literalIndex) := by
  rw [variableGaugeCanonicalIncidenceRoutes_of_clause_mem
    source placement gauge routes clauseMember]
  exact unitSubdivisionDirections_translatePolyline _ _

end PositionedPeriodicCNF
end LeanTrominoes
