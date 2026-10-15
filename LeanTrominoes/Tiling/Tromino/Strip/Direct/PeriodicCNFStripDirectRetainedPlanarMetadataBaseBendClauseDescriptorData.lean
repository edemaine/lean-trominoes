/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.SAT.CNF.FormulaShape.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBaseBendScanData
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Route.PeriodicCNFStripDirectSourceRouteDescriptorPairFieldTagData

/-! # Direct untranslated retained-bend descriptors -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)

/-- Direct-source bend descriptors after quotienting the nine translated
physical copies by periodic normalization. -/
def directRetainedPlanarMetadataBaseBendClauseDescriptors
    (symbols : List encoding.Γ) :
    List FormulaShapeDirectionOrdering.Token :=
  PeriodicOrthocrossing.RouteDescriptorPairAffine.affineBaseBendDescriptorStream
    (directSourceRouteDescriptorPairFieldTags decider symbols)

abbrev DirectRetainedPlanarMetadataBaseBendClauseDescriptorCompiler :=
  @TM2ComputableInPolyTime
    (List encoding.Γ)
    (List FormulaShapeDirectionOrdering.Token)
    encoding.Γ FormulaShapeDirectionOrdering.Token id id
    (directRetainedPlanarMetadataBaseBendClauseDescriptors decider)

end LeanTrominoes.PeriodicCNFStripReduction

end
