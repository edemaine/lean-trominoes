/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeFiveFamilyNormalizedClauses
import LeanTrominoes.PeriodicThreeSATThreeNonempty
import LeanTrominoes.PeriodicThreeSATThreeRoutedVariableRotatedEdgeIndexDedup
import LeanTrominoes.RetainedAngularFanFinalCoordinatedRouteValidity

/-! # Scaled route lengths after the three-occurrence reduction -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicOrthocrossing
open PeriodicThreeSATThree

local instance finalThreeSATThreeScaledLengthDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq (ThreeOccurrenceVariable Variable) :=
  fiveFamilyNormalizedThreeOccurrenceDecidableEq

/-- Every genuine final incidence of the three-occurrence formula retains at
least two points after source-clearance scaling. -/
theorem finalCoordinatedScaledThreeSATThreeSourceRoute_length_ge_two
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceClausesNonempty : ∀ clause ∈ source.clauses, clause ≠ [])
    {clause : PositionedPeriodicClause
      (WrappedPeriodicPlanarSATVariable
        (ThreeOccurrenceVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (finalCoordinatedSource
          (PeriodicThreeSATThree.formula source)).clauses.zipIdx)
    {literal : PeriodicLiteral
      (WrappedPeriodicPlanarSATVariable
        (ThreeOccurrenceVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    2 ≤ (scalePolyline retainedAngularFanSourceClearanceFactor
      (finalCoordinatedSourceRoutes
        (PeriodicThreeSATThree.formula source)
        clauseIndex literalIndex)).length := by
  exact finalCoordinatedScaledSourceRoute_length_ge_two
    (PeriodicThreeSATThree.formula source)
    (PeriodicThreeSATThree.formula_isLocal sourceLocal)
    (PeriodicThreeSATThree.formula_widthAtMostThree sourceWidth)
    (PeriodicThreeSATThree.formula_occurrencesAtMostThree_decidableEq source)
    (PeriodicThreeSATThree.formula_clausesNonempty
      source sourceClausesNonempty)
    clauseMember literalMember

end PeriodicEightOccurrenceSplit
end LeanTrominoes
