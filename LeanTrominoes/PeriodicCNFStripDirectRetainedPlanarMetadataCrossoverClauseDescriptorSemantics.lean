/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFProgramSource
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataCrossoverClauseDescriptorData
import LeanTrominoes.ThirteenMarkerPairBlockSemantics

/-! # Semantics of compiled fixed crossover descriptors -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


local instance directRetainedCrossoverClauseSemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

theorem directRetainedPlanarMetadataCompiledCrossoverClauseDescriptors_eq_fixed
    (symbols : List encoding.Γ) :
    directRetainedPlanarMetadataCompiledCrossoverClauseDescriptors
        decider symbols =
      directRetainedPlanarMetadataFixedCrossoverClauseDescriptors
        decider symbols := by
  unfold directRetainedPlanarMetadataCompiledCrossoverClauseDescriptors
    directRetainedPlanarMetadataCrossingMarkers
    directRetainedPlanarMetadataFixedCrossoverClauseDescriptors
  rw [ThirteenMarkerPairBlocks.output_replicate_mul_thirteen]
  have blockEq :
      ThirteenMarkerPairBlocks.block
          FormulaShapeCrossoverDirection.descriptorPair =
        FormulaShapeCrossoverDirection.descriptors :=
    FormulaShapeCrossoverDirection.pairedDescriptors_eq_descriptors
  rw [blockEq]

end LeanTrominoes.PeriodicCNFStripReduction

end
