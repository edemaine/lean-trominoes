/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PositionedPeriodicCNFVariableGaugeDrawing
import LeanTrominoes.PositionedPeriodicCNFVariableGaugeRouteBranchComputability
import LeanTrominoes.PositionedPeriodicCNFVariableGaugeSelectedClauseComputability

/-! # Variable-gauge canonical incidence-route computability -/

noncomputable section

namespace LeanTrominoes
namespace PositionedPeriodicCNF

theorem variableGaugeCanonicalIncidenceRoutes_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (source : Input → PositionedPeriodicCNF Variable)
    (placement : Input → PeriodicVariablePlacement Variable)
    (gauge : Input → Variable → Cell)
    (routes : Input → IncidenceRoutes)
    (sourcePrimrec : Primrec source)
    (periodPrimrec : Primrec fun input => (placement input).period)
    (gaugePrimrec : Primrec fun input : Input × Variable =>
      gauge input.1 input.2)
    (routesPrimrec : Primrec fun input : (Input × Nat) × Nat =>
      routes input.1.1 input.1.2 input.2) :
    Primrec fun input : (Input × Nat) × Nat =>
      variableGaugeCanonicalIncidenceRoutes
        (source input.1.1) (placement input.1.1) (gauge input.1.1)
        (routes input.1.1) input.1.2 input.2 := by
  let Query := (Input × Nat) × Nat
  have selected : Primrec fun input : Query =>
      (source input.1.1).clauses[input.1.2]? :=
    selectedRouteClause?_primrec source sourcePrimrec
  have some : Primrec₂ fun (input : Query)
      (clause : PositionedPeriodicClause Variable) =>
      variableGaugeRouteBranch
        (fun query => (placement query).period) gauge routes
        (input, clause) := by
    exact (variableGaugeRouteBranch_primrec
      (fun input => (placement input).period) gauge routes
      periodPrimrec gaugePrimrec routesPrimrec).to₂
  exact (Primrec.option_casesOn selected (Primrec.const []) some).of_eq
    fun input => by
      unfold variableGaugeCanonicalIncidenceRoutes
      cases (source input.1.1).clauses[input.1.2]? <;> rfl

end PositionedPeriodicCNF
end LeanTrominoes
