/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataClauseDescriptorFamilyData
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataCrossoverClauseDescriptorData

/-! # Fixed-crossover assembly of direct clause-descriptor candidates -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directRetainedFixedCrossoverAssemblyDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The already-deduplicated fixed crossover prefix followed by the carrier,
bend, routed-clause, and routed-variable descriptor scans. -/
def directRetainedPlanarMetadataFixedCrossoverClauseDescriptorAssembly
    (symbols : List encoding.Γ) :
    List FormulaShapeDirectionOrdering.Token :=
  directRetainedPlanarMetadataFixedCrossoverClauseDescriptors
      decider symbols ++
    directRetainedPlanarMetadataCarrierClauseDescriptorSuffix decider symbols

abbrev DirectRetainedPlanarMetadataFixedCrossoverClauseDescriptorAssemblyCompiler :=
  @TM2ComputableInPolyTime
    (List encoding.Γ) (List FormulaShapeDirectionOrdering.Token)
    encoding.Γ FormulaShapeDirectionOrdering.Token id id
    (directRetainedPlanarMetadataFixedCrossoverClauseDescriptorAssembly decider)

end LeanTrominoes.PeriodicCNFStripReduction

end
