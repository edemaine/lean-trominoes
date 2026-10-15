/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectRetainedPlanarMetadataClauseDescriptorFamilyData
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectRetainedPlanarMetadataCrossoverClauseDescriptorData

/-! # Fixed-crossover assembly of direct clause-descriptor candidates -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


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
