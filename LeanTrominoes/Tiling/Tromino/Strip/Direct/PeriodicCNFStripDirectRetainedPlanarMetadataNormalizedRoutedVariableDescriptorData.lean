/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.SAT.CNF.FormulaShape.PeriodicCNFFormulaShapeRetainedPlanarMetadataNormalizedRoutedVariablePairCompiledData
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Route.PeriodicCNFStripDirectSourceRouteDescriptorPairFieldTagData

/-! # Direct normalized routed-variable descriptors -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


/-- Evaluate the normalized routed-variable pair scan on the direct source's
exact tagged descriptor square. -/
def directRetainedPlanarMetadataNormalizedRoutedVariableClauseDescriptors
    (symbols : List encoding.Γ) :
    List FormulaShapeDirectionOrdering.Token :=
  FormulaShapeRetainedPlanarMetadataDirection.compiledNormalizedRoutedVariablePairDescriptorStream
    (directSourceRouteDescriptorPairFieldTags decider symbols)

abbrev
    DirectRetainedPlanarMetadataNormalizedRoutedVariableClauseDescriptorCompiler :=
  @TM2ComputableInPolyTime
    (List encoding.Γ)
    (List FormulaShapeDirectionOrdering.Token)
    encoding.Γ FormulaShapeDirectionOrdering.Token id id
    (directRetainedPlanarMetadataNormalizedRoutedVariableClauseDescriptors
      decider)

end LeanTrominoes.PeriodicCNFStripReduction

end
