/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.SAT.CNF.FormulaShape.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierCompactWordMaskSemantics
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Carrier.PeriodicCNFStripDirectSourceCarrierCompactAtomWordPairSemanticData
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Formula.PeriodicCNFStripDirectSourceFormulaForwardLocalNamed
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Formula.PeriodicCNFStripDirectSourceFormulaIncidenceDegree
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Route.PeriodicCNFStripDirectSourceRouteDescriptorCrossingMarkers

/-! # Direct-source compact pairs selected by the retained mask -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


local instance directCarrierCompactPairMaskVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The direct retained compact word pairs are the normalized semantic
carrier-link endpoint words for any source-variable word assignment. -/
theorem directSourceCarrierCompactAtomWordPairMaskTarget_eq_normalizedWords
    (sourceWord : Variable → List Bool)
    (symbols : List encoding.Γ) :
    directSourceCarrierCompactAtomWordPairMaskTarget decider symbols =
      directSourceCarrierNormalizedCompactAtomWordPairs
        decider sourceWord symbols := by
  let source := directSourceFormula decider symbols
  have wellFormed : source.incidenceGraph.IsWellFormed :=
    PeriodicCNF.incidenceGraph_isWellFormed source
  have degree : source.incidenceGraph.DegreeAtMost 3 := by
    exact directSourceFormula_incidenceGraph_degreeAtMost decider symbols
  have isLocal : source.incidenceGraph.IsLocal := by
    unfold source directSourceFormula
    exact PeriodicCNF.incidenceGraph_isLocal (sourceFormula_isLocal _)
  have forward : source.IsForwardLocal := by
    exact directSourceFormula_isForwardLocal decider symbols
  have nonempty : incidencesWithMetadata source ≠ [] := by
    exact directSource_incidencesWithMetadata_ne_nil decider symbols
  unfold directSourceCarrierCompactAtomWordPairMaskTarget
    directSourceCarrierNormalizedCompactAtomWordPairs
  exact congrArg DelimitedBinaryWordPairs.Input.mk
    (retainedCompactWordPairsByMask_eq_normalizedLinks
      source sourceWord wellFormed degree isLocal forward nonempty)

end PeriodicCNFStripReduction
end LeanTrominoes

end
