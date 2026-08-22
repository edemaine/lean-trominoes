/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeDirectionOrderingFormulaData
import LeanTrominoes.PlanarThreeSATIncidencePlanarity
import LeanTrominoes.ThirteenMarkerPairBlockData

/-! # Fixed finite direction descriptors of the crossover gadget -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeCrossoverDirection

open PlanarThreeSAT

/-- A fixed crossover clause with every periodic occurrence in the common
zero cell; the retained planar construction will be shown to have the same
finite literal profile. -/
def zeroOffsetClause (clause : EmbeddedClause CrossoverVariable) :
    PeriodicClause CrossoverVariable :=
  clause.literals.map fun literal =>
    ⟨literal.1, (0, 0), literal.2⟩

/-- The twenty-six fixed clause-profile/first-direction descriptors of one
Figure 8(b) crossover. -/
def descriptors : List FormulaShapeDirectionOrdering.Token :=
  crossoverFormula.zipIdx.map fun taggedClause =>
    .clause
      (FormulaShapeDirectionOrdering.DirectedClauseProfile.ofClause
        crossoverStraightIncidenceDrawing.routes taggedClause.2
        ⟨(0, 0), zeroOffsetClause taggedClause.1⟩)

/-- Two consecutive fixed crossover descriptors emitted at one position of
a thirteen-marker group. -/
def descriptorPair (index : Fin 13) :
    List FormulaShapeDirectionOrdering.Token :=
  (descriptors.drop (2 * index.val)).take 2

/-- The block presentation consumed by the finite-state thirteen-marker
postprocessor. -/
def pairedDescriptors : List FormulaShapeDirectionOrdering.Token :=
  ThirteenMarkerPairBlocks.block descriptorPair

end FormulaShapeCrossoverDirection
end PeriodicCNF
end LeanTrominoes
