/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PositionedPeriodicCNFVariableGauge

/-! # Literal-value projection through positioned variable gauges -/

namespace LeanTrominoes
namespace PositionedPeriodicCNF

/-- A positioned variable gauge changes atoms' stored offsets but preserves
the complete clause-major literal-value presentation. -/
@[simp] theorem variableGauge_clauseLiteralValues
    {Variable : Type}
    (source : PositionedPeriodicCNF Variable)
    (gauge : Variable → Cell) :
    ((source.variableGauge gauge).clauses.map fun clause =>
        clause.literals.map PeriodicLiteral.value) =
      (source.clauses.map fun clause =>
        clause.literals.map PeriodicLiteral.value) := by
  simp [PositionedPeriodicCNF.variableGauge,
    PeriodicClause.variableGauge, List.map_map]

end PositionedPeriodicCNF
end LeanTrominoes
