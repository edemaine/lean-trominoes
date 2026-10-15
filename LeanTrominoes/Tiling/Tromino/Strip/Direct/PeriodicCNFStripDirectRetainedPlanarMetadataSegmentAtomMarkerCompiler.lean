/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectRetainedPlanarMetadataSegmentAtomMarkerData
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Formula.PeriodicCNFStripDirectSourceFormulaShapeCompiler
import LeanTrominoes.Computation.Encoding.Finite.FiniteBlockTransducer
import LeanTrominoes.Computation.TM2.TM2CompositionMachine

/-! # Polynomial-time combined segment and atom markers -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


noncomputable def
    directRetainedPlanarMetadataSegmentAtomMarkersComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ)
      (List PeriodicCNF.FormulaShapeDirectionOrdering.Token)
      encoding.Γ PeriodicCNF.FormulaShapeDirectionOrdering.Token
      id id (directRetainedPlanarMetadataSegmentAtomMarkers decider) := by
  let shape := directSourceFormulaShapeComputableInPolyTime decider
  let extract := FiniteBlockTransducer.computableInPolyTime
    retainedSegmentAtomMarkerBlock
  let complete := TM2CompositionMachine.computableInPolyTime shape extract
  exact complete

end LeanTrominoes.PeriodicCNFStripReduction
