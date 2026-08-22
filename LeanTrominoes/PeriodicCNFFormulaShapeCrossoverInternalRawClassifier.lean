/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeCrossoverInternalClassifierData

/-! # Raw planar-SAT classifier for crossover-internal atoms -/

namespace LeanTrominoes
namespace PeriodicCNF

open PeriodicOrthocrossing

namespace FormulaShapeRetainedPlanarMetadataDirection

/-- Whether a finite planar-SAT atom belongs to the crossover-internal
summand. -/
def planarSATAtomIsCrossoverInternal
    {Variable : Type}
    (atom : PlanarSATVariable Variable) : Bool :=
  match atom with
  | .inr _ => true
  | .inl _ => false

/-- Whether a finite embedded planar-SAT clause contains a crossover-internal
atom. -/
def embeddedClauseHasCrossoverInternal
    {Variable : Type}
    (clause : PlanarThreeSAT.EmbeddedClause (PlanarSATVariable Variable)) :
    Bool :=
  clause.literals.any fun literal =>
    planarSATAtomIsCrossoverInternal literal.1

/-- Periodicizing and wrapping one atom preserves whether it is a crossover
internal. -/
@[simp]
theorem wrappedAtomIsCrossoverInternal_normalizePlanarSATVariable
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : PlanarSATVariable Variable) :
    wrappedAtomIsCrossoverInternal
        (⟨(normalizePlanarSATVariable source atom).1⟩ :
          WrappedPeriodicPlanarSATVariable Variable) =
      planarSATAtomIsCrossoverInternal atom := by
  cases atom with
  | inl node =>
      cases node with
      | carrier carrier => cases carrier <;> rfl
      | atom atom => rfl
  | inr internal => rfl

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
