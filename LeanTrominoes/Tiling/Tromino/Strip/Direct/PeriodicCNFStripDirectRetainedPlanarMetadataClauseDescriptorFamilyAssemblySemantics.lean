/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectRetainedPlanarMetadataClauseDescriptorFamilySemantics

/-! # Exact assembly of direct retained descriptor families -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


theorem directRetainedPlanarMetadataAssembledFamilyClauseDescriptors_eq
    (symbols : List encoding.Γ) :
    directRetainedPlanarMetadataAssembledFamilyClauseDescriptors
        decider symbols =
      directRetainedPlanarMetadataFamilyClauseDescriptors decider symbols := by
  unfold directRetainedPlanarMetadataAssembledFamilyClauseDescriptors
    directRetainedPlanarMetadataCarrierClauseDescriptorSuffix
    directRetainedPlanarMetadataBendClauseDescriptorSuffix
    directRetainedPlanarMetadataRoutedClauseDescriptorSuffix
    directRetainedPlanarMetadataFamilyClauseDescriptors
    directRetainedPlanarMetadataCrossoverClauseDescriptors
    directRetainedPlanarMetadataCarrierClauseDescriptors
    directRetainedPlanarMetadataBendClauseDescriptors
    directRetainedPlanarMetadataRoutedClauseDescriptors
    directRetainedPlanarMetadataRoutedVariableClauseDescriptors
    FormulaShapeRetainedPlanarMetadataDirection.familyMetadataClauseDescriptors
    FormulaShapeRetainedPlanarMetadataDirection.crossoverMetadataClauseDescriptors
    FormulaShapeRetainedPlanarMetadataDirection.carrierMetadataClauseDescriptors
    FormulaShapeRetainedPlanarMetadataDirection.bendMetadataClauseDescriptors
    FormulaShapeRetainedPlanarMetadataDirection.routedClauseMetadataClauseDescriptors
    FormulaShapeRetainedPlanarMetadataDirection.routedVariableMetadataClauseDescriptors
  simp only [List.append_assoc]

end LeanTrominoes.PeriodicCNFStripReduction

end
