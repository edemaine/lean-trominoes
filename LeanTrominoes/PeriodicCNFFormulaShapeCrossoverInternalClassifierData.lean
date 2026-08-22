/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeCrossoverClauseGauge

/-! # Classifier for crossover-internal atoms in normalized clauses -/

namespace LeanTrominoes
namespace PeriodicCNF

open PeriodicOrthocrossing PlanarThreeSAT

namespace FormulaShapeRetainedPlanarMetadataDirection

/-- Whether a fixed Figure 8(b) role is internal rather than one of its four
boundary ports. -/
def crossoverRoleIsInternal : CrossoverVariable → Bool
  | .aLeft | .aRight | .bTop | .bBottom => false
  | _ => true

/-- Whether a wrapped periodic planar-SAT atom is a crossover-internal atom. -/
def wrappedAtomIsCrossoverInternal
    {Variable : Type}
    (atom : WrappedPeriodicPlanarSATVariable Variable) : Bool :=
  match atom.original with
  | .crossoverInternal _ => true
  | _ => false

/-- Whether a normalized periodic clause contains a crossover-internal atom. -/
def normalizedClauseHasCrossoverInternal
    {Variable : Type}
    (clause :
      PeriodicClause (WrappedPeriodicPlanarSATVariable Variable)) : Bool :=
  clause.any fun literal =>
    wrappedAtomIsCrossoverInternal literal.atom

@[simp]
theorem wrappedAtomIsCrossoverInternal_normalizedCrossoverAtom
    {Variable : Type}
    (crossing : CrossingRecord)
    (role : CrossoverVariable) :
    wrappedAtomIsCrossoverInternal
        (⟨normalizedCrossoverAtom crossing role⟩ :
          WrappedPeriodicPlanarSATVariable Variable) =
      crossoverRoleIsInternal role := by
  cases role <;> rfl

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
