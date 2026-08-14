/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PositionedPeriodicCNFVariableGaugeKnownRouteComputability

/-! # Variable-gauge successful route-lookup branch computability -/

noncomputable section

namespace LeanTrominoes
namespace PositionedPeriodicCNF

def variableGaugeRouteBranch {Input Variable : Type*}
    (period : Input → Nat)
    (gauge : Input → Variable → Cell)
    (routes : Input → IncidenceRoutes)
    (input : ((Input × Nat) × Nat) ×
      PositionedPeriodicClause Variable) : List Cell :=
  variableGaugeKnownRoute
    (fun query => period query.1.1.1)
    (fun query => gauge query.1.1.1)
    Prod.snd
    (fun query => routes query.1.1.1 query.1.1.2 query.1.2)
    input

theorem variableGaugeRouteBranch_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (period : Input → Nat)
    (gauge : Input → Variable → Cell)
    (routes : Input → IncidenceRoutes)
    (periodPrimrec : Primrec period)
    (gaugePrimrec : Primrec fun input : Input × Variable =>
      gauge input.1 input.2)
    (routesPrimrec : Primrec fun input : (Input × Nat) × Nat =>
      routes input.1.1 input.1.2 input.2) :
    Primrec (variableGaugeRouteBranch period gauge routes) := by
  let Combined := ((Input × Nat) × Nat) ×
    PositionedPeriodicClause Variable
  exact variableGaugeKnownRoute_primrec
    (Input := Combined)
    (fun query => period query.1.1.1)
    (fun query => gauge query.1.1.1)
    Prod.snd
    (fun query => routes query.1.1.1 query.1.1.2 query.1.2)
    (periodPrimrec.comp
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
    (gaugePrimrec.comp
      (Primrec.pair
        (Primrec.fst.comp
          (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
        Primrec.snd))
    Primrec.snd
    (routesPrimrec.comp Primrec.fst)

end PositionedPeriodicCNF
end LeanTrominoes
