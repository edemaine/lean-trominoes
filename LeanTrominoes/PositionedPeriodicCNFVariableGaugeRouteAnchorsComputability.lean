/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PositionedPeriodicCNFVariableGaugeClauseLiteralsComputability

/-! # Variable-gauge route-anchor computability -/

noncomputable section

namespace LeanTrominoes
namespace PositionedPeriodicCNF

def variableGaugeRouteAnchors {Input Variable : Type*}
    (gauge : Input → Variable → Cell)
    (clause : Input → PositionedPeriodicClause Variable)
    (input : Input) : Cell × Cell :=
  (PeriodicCNF.clauseAnchor (clause input).literals,
    PeriodicCNF.clauseAnchor
      (variableGaugeClauseLiterals gauge clause input))

theorem variableGaugeRouteAnchors_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (gauge : Input → Variable → Cell)
    (clause : Input → PositionedPeriodicClause Variable)
    (gaugePrimrec : Primrec fun input : Input × Variable =>
      gauge input.1 input.2)
    (clausePrimrec : Primrec clause) :
    Primrec (variableGaugeRouteAnchors gauge clause) := by
  have literals : Primrec fun input => (clause input).literals :=
    PositionedPeriodicClause.literals_primrec.comp clausePrimrec
  exact Primrec.pair
    (PeriodicCNF.clauseAnchor_primrec.comp literals)
    (PeriodicCNF.clauseAnchor_primrec.comp
      (variableGaugeClauseLiterals_primrec gauge clause
        gaugePrimrec clausePrimrec))

end PositionedPeriodicCNF
end LeanTrominoes
