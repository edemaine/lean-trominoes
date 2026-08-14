/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingConstructionComputability
import LeanTrominoes.PositionedPeriodicCNFVariableGaugeRouteTranslationComputability

/-! # Variable-gauge known-clause route computability -/

noncomputable section

namespace LeanTrominoes
namespace PositionedPeriodicCNF

def variableGaugeKnownRoute {Input Variable : Type*}
    (period : Input → Nat)
    (gauge : Input → Variable → Cell)
    (clause : Input → PositionedPeriodicClause Variable)
    (route : Input → List Cell) (input : Input) : List Cell :=
  PeriodicOrthocrossing.translatePolyline
    (variableGaugeCanonicalRouteTranslation period gauge clause input)
    (route input)

theorem variableGaugeKnownRoute_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (period : Input → Nat)
    (gauge : Input → Variable → Cell)
    (clause : Input → PositionedPeriodicClause Variable)
    (route : Input → List Cell)
    (periodPrimrec : Primrec period)
    (gaugePrimrec : Primrec fun input : Input × Variable =>
      gauge input.1 input.2)
    (clausePrimrec : Primrec clause)
    (routePrimrec : Primrec route) :
    Primrec (variableGaugeKnownRoute period gauge clause route) := by
  exact PeriodicOrthocrossing.translatePolyline_primrec.comp
    (variableGaugeCanonicalRouteTranslation_primrec period gauge clause
      periodPrimrec gaugePrimrec clausePrimrec)
    routePrimrec

end PositionedPeriodicCNF
end LeanTrominoes
