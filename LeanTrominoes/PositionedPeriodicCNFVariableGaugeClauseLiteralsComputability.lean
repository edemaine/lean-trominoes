/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFGaugeComputability
import LeanTrominoes.PositionedPeriodicCNFComputability

/-! # Gauged positioned-clause literal computability -/

noncomputable section

namespace LeanTrominoes
namespace PositionedPeriodicCNF

def variableGaugeClauseLiterals {Input Variable : Type*}
    (gauge : Input → Variable → Cell)
    (clause : Input → PositionedPeriodicClause Variable)
    (input : Input) : PeriodicClause Variable :=
  (clause input).literals.variableGauge (gauge input)

theorem variableGaugeClauseLiterals_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (gauge : Input → Variable → Cell)
    (clause : Input → PositionedPeriodicClause Variable)
    (gaugePrimrec : Primrec fun input : Input × Variable =>
      gauge input.1 input.2)
    (clausePrimrec : Primrec clause) :
    Primrec (variableGaugeClauseLiterals gauge clause) := by
  have literals : Primrec fun input => (clause input).literals :=
    PositionedPeriodicClause.literals_primrec.comp clausePrimrec
  exact ((PeriodicClause.variableGauge_primrec gauge gaugePrimrec).comp
    (Primrec.pair Primrec.id literals)).of_eq fun _ => rfl

end PositionedPeriodicCNF
end LeanTrominoes
