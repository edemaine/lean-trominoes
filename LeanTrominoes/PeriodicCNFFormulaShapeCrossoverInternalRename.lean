/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeCrossoverInternalRawClassifier

/-! # Absence of crossover internals under external renaming -/

namespace LeanTrominoes
namespace PeriodicCNF

open PeriodicOrthocrossing PlanarThreeSAT

namespace FormulaShapeRetainedPlanarMetadataDirection

/-- Renaming through a map that avoids the internal summand produces a clause
with no crossover-internal atom. -/
theorem embeddedClauseHasCrossoverInternal_rename_eq_false
    {Variable Source : Type}
    (clause : EmbeddedClause Source)
    (variableMap : Source → PlanarSATVariable Variable)
    (outside : ∀ atom,
      planarSATAtomIsCrossoverInternal (variableMap atom) = false) :
    embeddedClauseHasCrossoverInternal
        (clause.rename variableMap) = false := by
  unfold embeddedClauseHasCrossoverInternal
    EmbeddedClause.rename EmbeddedClause.map
  induction clause.literals with
  | nil => rfl
  | cons literal literals induction =>
    simp only [List.map_cons, List.any_cons]
    rw [outside literal.1, Bool.false_or, induction]

/-- The external clause/variable-gadget embedding never creates a crossover
internal. -/
theorem embeddedClauseHasCrossoverInternal_rename_external_eq_false
    {Variable : Type}
    (clause : EmbeddedClause (PlanarSATNode Variable)) :
    embeddedClauseHasCrossoverInternal
        (clause.rename planarSATExternalVariableMap) = false := by
  apply embeddedClauseHasCrossoverInternal_rename_eq_false
  intro atom
  rfl

/-- Embedding a carrier-node formula into the route core never creates a
crossover internal. -/
theorem embeddedClauseHasCrossoverInternal_rename_coreCarrier_eq_false
    {Variable : Type}
    (clause : EmbeddedClause CarrierNode) :
    embeddedClauseHasCrossoverInternal
        (clause.rename fun node =>
          @planarSATCoreVariableMap Variable
            (Sum.inl node :
              Sum CarrierNode
                (CrossingRecord × CrossoverInternal))) = false := by
  apply embeddedClauseHasCrossoverInternal_rename_eq_false
  intro atom
  rfl

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
