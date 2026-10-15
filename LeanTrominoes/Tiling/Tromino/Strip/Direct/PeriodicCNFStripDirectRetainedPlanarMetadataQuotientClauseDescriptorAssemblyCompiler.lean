/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectRetainedPlanarMetadataCrossoverClauseDescriptorFixedCompiler
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectRetainedPlanarMetadataQuotientCarrierClauseDescriptorSuffixCompiler
import LeanTrominoes.Computation.TM2.TM2NativeListAppendClosure

/-! # Compiling the per-family quotient descriptor assembly -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


/-- The fixed crossover prefix appends to the independently compiled
quotiented four-family suffix. -/
noncomputable def
    directRetainedPlanarMetadataQuotientClauseDescriptorAssemblyComputableInPolyTime :
    DirectRetainedPlanarMetadataQuotientClauseDescriptorAssemblyCompiler
      decider := by
  let complete := TM2ListAppend.nativeComputableInPolyTime
    (directRetainedPlanarMetadataFixedCrossoverClauseDescriptorsComputableInPolyTime
      decider)
    (directRetainedPlanarMetadataQuotientCarrierClauseDescriptorSuffixComputableInPolyTime
      decider)
  change @TM2ComputableInPolyTime
    (List encoding.Γ)
    (List FormulaShapeDirectionOrdering.Token)
    encoding.Γ FormulaShapeDirectionOrdering.Token id id
    (fun symbols =>
      directRetainedPlanarMetadataFixedCrossoverClauseDescriptors
          decider symbols ++
        directRetainedPlanarMetadataQuotientCarrierClauseDescriptorSuffix
          decider symbols)
  exact complete

end LeanTrominoes.PeriodicCNFStripReduction

end
