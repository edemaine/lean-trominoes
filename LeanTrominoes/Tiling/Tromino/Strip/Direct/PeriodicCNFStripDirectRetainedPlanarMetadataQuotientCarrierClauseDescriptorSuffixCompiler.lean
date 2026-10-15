/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectRetainedPlanarMetadataCarrierClauseDescriptorCompiler
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectRetainedPlanarMetadataQuotientBendClauseDescriptorSuffixCompiler
import LeanTrominoes.Computation.TM2.TM2NativeListAppendClosure

/-! # Compiling the quotiented carrier descriptor suffix -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


noncomputable def
    directRetainedPlanarMetadataQuotientCarrierClauseDescriptorSuffixComputableInPolyTime :
    DirectRetainedPlanarMetadataQuotientCarrierClauseDescriptorSuffixCompiler
      decider := by
  change @TM2ComputableInPolyTime
    (List encoding.Γ)
    (List FormulaShapeDirectionOrdering.Token)
    encoding.Γ FormulaShapeDirectionOrdering.Token id id
    (fun symbols =>
      directRetainedPlanarMetadataCarrierClauseDescriptors
          decider symbols ++
        directRetainedPlanarMetadataQuotientBendClauseDescriptorSuffix
          decider symbols)
  exact TM2ListAppend.nativeComputableInPolyTime
    (directRetainedPlanarMetadataCarrierClauseDescriptorsComputableInPolyTime
      decider)
    (directRetainedPlanarMetadataQuotientBendClauseDescriptorSuffixComputableInPolyTime
      decider)

end LeanTrominoes.PeriodicCNFStripReduction

end
