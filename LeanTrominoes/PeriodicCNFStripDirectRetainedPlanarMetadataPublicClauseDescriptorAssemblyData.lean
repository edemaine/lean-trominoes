/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataClauseDescriptorFamilyData
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataCrossoverClauseDescriptorData

/-! # Fixed-crossover assembly of direct public clause descriptors -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directRetainedPublicAssemblyDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The already-deduplicated fixed crossover prefix followed by the carrier,
bend, routed-clause, and routed-variable descriptor scans. -/
def directRetainedPlanarMetadataAssembledPublicClauseDescriptors
    (symbols : List encoding.Γ) :
    List FormulaShapeDirectionOrdering.Token :=
  directRetainedPlanarMetadataFixedCrossoverClauseDescriptors
      decider symbols ++
    directRetainedPlanarMetadataCarrierClauseDescriptorSuffix decider symbols

abbrev DirectRetainedPlanarMetadataAssembledPublicClauseDescriptorCompiler :=
  @TM2ComputableInPolyTime
    (List encoding.Γ) (List FormulaShapeDirectionOrdering.Token)
    encoding.Γ FormulaShapeDirectionOrdering.Token id id
    (directRetainedPlanarMetadataAssembledPublicClauseDescriptors decider)

end LeanTrominoes.PeriodicCNFStripReduction

end
