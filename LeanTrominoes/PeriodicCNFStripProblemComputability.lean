/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripPlanarReduction
import LeanTrominoes.PeriodicCNFStripSourceFormulaComputability
import LeanTrominoes.PeriodicCNFPlanarRetainedPolarityNormalizedRibbonThreeDMComputability

/-!
# Computability of the strip reduction's planar 3DM problem

The semantic reduction packages a continuously planar presentation and hence
contains proof arguments.  Its finite 3DM problem is nevertheless exactly the
output of the proof-free retained polarity-normalization compiler.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

local instance stripProblemComputabilityVariableDecidableEq :
    DecidableEq Variable :=
  Classical.decEq _

/-- The finite 3DM endpoint with all geometric proof arguments erased. -/
def computedProblem (source : PeriodicCNF Nat) : PeriodicThreeDM :=
  _root_.LeanTrominoes.PeriodicOrthocrossing.retainedOrderedFixedEightPolarityNormalizedPaddedPeriodicThreeDMProblemComputed
    (sourceFormula source)

/-- The proof-free endpoint is primitive recursive in the guarded source. -/
theorem computedProblem_primrec : Primrec computedProblem :=
  _root_.LeanTrominoes.PeriodicOrthocrossing.retainedOrderedFixedEightPolarityNormalizedPaddedPeriodicThreeDMProblemComputed_primrec.comp
    sourceFormula_primrec

theorem computedProblem_computable : Computable computedProblem :=
  computedProblem_primrec.to_comp

/-- The runtime endpoint is exactly the finite problem carried by the
continuously planar semantic presentation. -/
theorem computedProblem_eq_problem (source : PeriodicCNF Nat) :
    computedProblem source = problem source := by
  unfold computedProblem problem
  exact
    _root_.LeanTrominoes.PeriodicOrthocrossing.retainedOrderedFixedEightPolarityNormalizedPaddedPeriodicThreeDMProblemComputed_eq
      (sourceFormula source)
      (sourceFormula_isLocal source)
      (sourceFormula_widthAtMostThree source)
      (sourceFormula_occurrencesAtMostThree_canonicalBEq source)
      (sourceFormula_clausesNonempty source)

/-- Although `problem` is defined through a proof-backed presentation
pipeline, its finite data are primitive recursive. -/
theorem problem_primrec : Primrec problem :=
  computedProblem_primrec.of_eq computedProblem_eq_problem

theorem problem_computable : Computable problem :=
  problem_primrec.to_comp

end PeriodicCNFStripReduction
end LeanTrominoes
