/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.SAT.CNF.FormulaShape.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendScanData
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectRetainedPlanarMetadataClauseDescriptorFamilyData
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Route.PeriodicCNFStripDirectSourceRouteDescriptorPairFieldTagData

/-! # Direct retained bend descriptors from affine route pairs -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)

/-- Apply the compact affine bend scan to the direct source's tagged
descriptor-pair stream. -/
def directRetainedPlanarMetadataCompiledBendClauseDescriptors
    (symbols : List encoding.Γ) :
    List PeriodicCNF.FormulaShapeDirectionOrdering.Token :=
  PeriodicOrthocrossing.RouteDescriptorPairAffine.affineBendDescriptorStream
    (directSourceRouteDescriptorPairFieldTags decider symbols)

abbrev DirectRetainedPlanarMetadataCompiledBendClauseDescriptorCompiler :=
  @TM2ComputableInPolyTime
    (List encoding.Γ)
    (List PeriodicCNF.FormulaShapeDirectionOrdering.Token)
    encoding.Γ PeriodicCNF.FormulaShapeDirectionOrdering.Token id id
    (directRetainedPlanarMetadataCompiledBendClauseDescriptors decider)

end LeanTrominoes.PeriodicCNFStripReduction

end
