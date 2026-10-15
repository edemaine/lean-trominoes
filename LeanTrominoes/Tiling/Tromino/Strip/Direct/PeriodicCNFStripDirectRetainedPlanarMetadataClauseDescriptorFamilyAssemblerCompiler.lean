/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectRetainedPlanarMetadataClauseDescriptorCarrierSuffixCompiler

/-! # Assembling all retained metadata clause-descriptor families -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


noncomputable def
    directRetainedPlanarMetadataFamilyClauseDescriptorsComputableInPolyTime
    (crossover :
      DirectRetainedPlanarMetadataCrossoverClauseDescriptorCompiler decider)
    (carried :
      DirectRetainedPlanarMetadataCarrierClauseDescriptorSuffixCompiler
        decider) :
    DirectRetainedPlanarMetadataAssembledFamilyClauseDescriptorCompiler
      decider := by
  change @TM2ComputableInPolyTime
    (List encoding.Γ) (List FormulaShapeDirectionOrdering.Token)
    encoding.Γ FormulaShapeDirectionOrdering.Token id id
    (fun symbols =>
      directRetainedPlanarMetadataCrossoverClauseDescriptors decider symbols ++
        directRetainedPlanarMetadataCarrierClauseDescriptorSuffix
          decider symbols)
  exact TM2ListAppend.nativeComputableInPolyTime crossover carried

end LeanTrominoes.PeriodicCNFStripReduction

end
