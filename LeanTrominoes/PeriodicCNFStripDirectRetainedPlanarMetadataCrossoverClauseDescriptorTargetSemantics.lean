/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeCrossoverClauseDescriptorFixed
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataCrossoverClauseDescriptorData
import LeanTrominoes.PeriodicCNFStripDirectSourceFormulaIncidenceDegree

/-! # Semantic target of direct fixed crossover descriptors -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directCrossoverTargetSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directCrossoverTargetSemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The direct fixed crossover stream is exactly the semantic descriptor
stream of the deduplicated normalized crossover clauses. -/
theorem directRetainedPlanarMetadataFixedCrossoverClauseDescriptors_eq_semantic
    (symbols : List encoding.Γ) :
    directRetainedPlanarMetadataFixedCrossoverClauseDescriptors
        decider symbols =
      ((crossoverMetadataNormalizedClauses
            (directSourceFormula decider symbols)).dedup).map
        canonicalCrossoverClauseDescriptor := by
  unfold directRetainedPlanarMetadataFixedCrossoverClauseDescriptors
  symm
  apply crossoverMetadataNormalizedClauses_dedup_map_descriptor_eq_fixed
  · exact PeriodicCNF.incidenceGraph_isWellFormed _
  · exact directSourceFormula_incidenceGraph_degreeAtMost decider symbols
  · unfold directSourceFormula
    exact PeriodicCNF.incidenceGraph_isLocal (sourceFormula_isLocal _)

end LeanTrominoes.PeriodicCNFStripReduction

end
