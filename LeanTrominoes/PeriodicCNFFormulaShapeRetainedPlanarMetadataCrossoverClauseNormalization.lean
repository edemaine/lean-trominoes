/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeCrossoverClauseGauge
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataDirectionData
import LeanTrominoes.PeriodicCNFPlanarDeduplicationWrapping

/-! # Normalized retained crossover metadata clauses -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- The final planar-SAT clause obtained from one fixed crossover template
clause at a specified physical crossing. -/
def crossoverClauseAt
    {Variable : Type}
    (crossing : CrossingRecord)
    (clause : EmbeddedClause CrossoverVariable) :
    EmbeddedClause (PlanarSATVariable Variable) :=
  (((clause.rename
      (scopedCrossoverVariableMap crossing
        (carrierNodeCrossingPorts crossing))).place
      (crossingMacroOrigin crossing) 1).rename
    (@planarSATCoreVariableMap Variable))

private theorem variableGauge_anchorNormalize_anchorNormalize
    {Variable : Type*}
    (gauge : Variable → Cell)
    (clause : PeriodicClause Variable) :
    ((clause.anchorNormalize).variableGauge gauge).anchorNormalize =
      (clause.variableGauge gauge).anchorNormalize := by
  cases clause with
  | nil =>
      rfl
  | cons first rest =>
      rcases first with ⟨firstAtom, ⟨anchorX, anchorY⟩, firstValue⟩
      rcases gauge firstAtom with ⟨gaugeX, gaugeY⟩
      simp [PeriodicClause.anchorNormalize,
        PeriodicClause.variableGauge,
        PeriodicLiteral.anchorNormalize,
        PeriodicLiteral.variableGauge,
        PeriodicCNF.clauseAnchor,
        List.map_map, Function.comp_def,
        Cell.add, Cell.sub]
      intro literal literalMember
      constructor <;> ring

/-- An actual neighboring-block crossover clause reduces to the canonical
wrapped zero-offset clause at its period-normalized crossing. -/
theorem normalizedClause_crossoverClauseAt_eq
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (degree : source.incidenceGraph.DegreeAtMost 3)
    (isLocal : source.incidenceGraph.IsLocal)
    (crossing : CrossingRecord)
    (crossingMember : crossing ∈ orientedCrossingHalo source.incidenceGraph)
    (clause : EmbeddedClause CrossoverVariable)
    (localClauseIndex : Nat) :
    normalizedClause source
        ⟨crossoverClauseAt crossing clause,
          .crossover crossing localClauseIndex⟩ =
      FormulaShapeCrossoverDirection.wrappedNormalizedClause
        (crossing.periodNormalize source.incidenceGraph) clause := by
  unfold normalizedClause crossoverClauseAt
  rw [← variableGauge_anchorNormalize_anchorNormalize]
  rw [← wrapPeriodicPlanarSATClause_anchorNormalize]
  rw [normalizedCrossoverClauseAt_eq]
  exact
    FormulaShapeCrossoverDirection.gaugedWrapped_normalizedCrossoverClause_eq
      source wellFormed
      (crossing.periodNormalize source.incidenceGraph)
      (periodNormalize_mem_orientedCrossings
        wellFormed degree isLocal crossingMember)
      clause

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
