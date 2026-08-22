/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeCrossoverGauge

/-! # Gauged normalized crossover clauses -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeCrossoverDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- The canonical wrapped presentation of one fixed crossover clause. -/
def wrappedNormalizedClause
    {Variable : Type*}
    (crossing : CrossingRecord)
    (clause : EmbeddedClause CrossoverVariable) :
    PeriodicClause (WrappedPeriodicPlanarSATVariable Variable) :=
  clause.literals.map fun literal =>
    ⟨⟨normalizedCrossoverAtom crossing literal.1⟩,
      (0, 0), literal.2⟩

/-- Canonical gauging is pointwise trivial on a normalized crossover
clause, and its common zero offset is already anchor-normalized. -/
theorem gaugedWrapped_normalizedCrossoverClause_eq
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (crossing : CrossingRecord)
    (crossingMember : crossing ∈ orientedCrossings formula.incidenceGraph)
    (clause : EmbeddedClause CrossoverVariable) :
    PeriodicClause.anchorNormalize
        ((wrapPeriodicPlanarSATClause
          (normalizedCrossoverClause
            (Variable := Variable) crossing clause)).variableGauge
          (retainedDrawingWrappedPeriodicPlanarSATVariableGauge formula)) =
      wrappedNormalizedClause crossing clause := by
  have gaugedEq :
      (wrapPeriodicPlanarSATClause
          (normalizedCrossoverClause
            (Variable := Variable) crossing clause)).variableGauge
        (retainedDrawingWrappedPeriodicPlanarSATVariableGauge formula) =
      wrappedNormalizedClause crossing clause := by
    unfold normalizedCrossoverClause wrappedNormalizedClause
      wrapPeriodicPlanarSATClause PeriodicClause.variableGauge
    simp only [List.map_map]
    apply List.map_congr_left
    intro literal _literalMember
    rcases literal with ⟨role, value⟩
    simp [wrapPeriodicPlanarSATLiteral,
      PeriodicLiteral.variableGauge,
      retainedGauge_normalizedCrossoverAtom_eq_zero
        formula wellFormed crossing crossingMember role,
      Cell.add]
  rw [gaugedEq]
  unfold wrappedNormalizedClause
  simpa [List.map_map, Function.comp_def] using
    PeriodicClause.anchorNormalize_uniform
      (clause.literals.map fun literal =>
        ((⟨normalizedCrossoverAtom crossing literal.1⟩ :
            WrappedPeriodicPlanarSATVariable Variable),
          literal.2))
      (0, 0)

end FormulaShapeCrossoverDirection
end PeriodicCNF
end LeanTrominoes
