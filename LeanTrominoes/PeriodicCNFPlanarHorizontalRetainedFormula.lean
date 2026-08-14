/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFOneDimensionalLists
import LeanTrominoes.PeriodicCNFPlanarHorizontalBends
import LeanTrominoes.PeriodicCNFPlanarHorizontalCrossovers
import LeanTrominoes.PeriodicCNFPlanarHorizontalRetainedCarrierEmbedding
import LeanTrominoes.PeriodicCNFPlanarHorizontalSourceClauses
import LeanTrominoes.PeriodicCNFPlanarHorizontalVariableArms
import LeanTrominoes.PeriodicCNFPlanarRetainedNormalizationComponents

/-!
# One-dimensional retained planar-SAT normalization

The retained anchor-normalized planar-SAT formula splits into crossover,
straight-carrier, bend, routed source-clause, and routed variable-arm
families.  Their component certificates combine to show that the complete
formula remains one dimensional for a horizontal local source incidence
graph.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- The complete retained anchor-normalized planar-SAT formula is one
dimensional when its source incidence graph is local and horizontal. -/
theorem
    retainedDrawingPeriodicPlanarSATFormula_anchorNormalize_isOneDimensional
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (isLocal : (PeriodicCNF.incidenceGraph formula).IsLocal)
    (horizontal :
      (PeriodicCNF.incidenceGraph formula).HasZeroVerticalOffsets) :
    (retainedDrawingPeriodicPlanarSATFormula
      formula).anchorNormalize.IsOneDimensional := by
  have crossingHorizontal :=
    normalizedScopedDrawingCrossoverClauses_isOneDimensional formula
  have carrierHorizontal :=
    embeddedNormalizedRetainedCompleteCarrierClauses_isOneDimensional
      isLocal horizontal
  have bendHorizontal :=
    embeddedNormalizedRouteBendClauses_isOneDimensional formula
  have sourceHorizontal :=
    normalizedRoutedClauseClauses_isOneDimensional formula
  have variableHorizontal :=
    normalizedDrawingRoutedVariableClauses_isOneDimensional
      formula horizontal
  have componentsHorizontal :=
    crossingHorizontal.append
      (carrierHorizontal.append
        (bendHorizontal.append
          (sourceHorizontal.append variableHorizontal)))
  intro clause clauseMember literal literalMember
  rw [
    retainedDrawingPeriodicPlanarSATFormula_anchorNormalize_five_components]
    at clauseMember
  exact componentsHorizontal clause clauseMember literal literalMember

/-- Formula-level locality and one-dimensionality supply the corresponding
incidence-graph hypotheses automatically. -/
theorem
    retainedDrawingPeriodicPlanarSATFormula_anchorNormalize_isOneDimensional_of_source
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (isLocal : formula.IsLocal)
    (horizontal : formula.IsOneDimensional) :
    (retainedDrawingPeriodicPlanarSATFormula
      formula).anchorNormalize.IsOneDimensional := by
  exact
    retainedDrawingPeriodicPlanarSATFormula_anchorNormalize_isOneDimensional
      (PeriodicCNF.incidenceGraph_isLocal isLocal)
      (PeriodicCNF.incidenceGraph_hasZeroVerticalOffsets horizontal)

end PeriodicOrthocrossing
end LeanTrominoes
