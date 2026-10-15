/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.SAT.CNF.FormulaShape.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariablePairStreamData
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Route.PeriodicCNFStripDirectSourceRouteDescriptorPairFieldTagData

/-! # Direct compiled routed-variable descriptor stream -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


/-- Run the finite routed-variable pair scan on the exact direct-source
descriptor-pair field stream. -/
def directRetainedPlanarMetadataCompiledRoutedVariableClauseDescriptors
    (symbols : List encoding.Γ) :
    List FormulaShapeDirectionOrdering.Token :=
  FormulaShapeRetainedPlanarMetadataDirection.compiledRoutedVariablePairDescriptorStream
    (directSourceRouteDescriptorPairFieldTags decider symbols)

abbrev DirectRetainedPlanarMetadataCompiledRoutedVariableClauseDescriptorCompiler :=
  @TM2ComputableInPolyTime
    (List encoding.Γ) (List FormulaShapeDirectionOrdering.Token)
    encoding.Γ FormulaShapeDirectionOrdering.Token id id
    (directRetainedPlanarMetadataCompiledRoutedVariableClauseDescriptors
      decider)

end LeanTrominoes.PeriodicCNFStripReduction

end
