/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFProgramSource
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataSegmentMarkerData
import LeanTrominoes.PeriodicCNFStripDirectSourceFormulaShapeCompiler
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.TM2CompositionMachine

/-! # Polynomial-time direct retained metadata segment markers -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


/-- The retained segment-marker phase is polynomial time: compile the guarded
formula shape, then replace every finite token by its fixed marker block. -/
noncomputable def
    directRetainedPlanarMetadataSegmentMarkersComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ)
      (List PeriodicCNF.FormulaShapeDirectionOrdering.Token)
      encoding.Γ PeriodicCNF.FormulaShapeDirectionOrdering.Token
      id id (directRetainedPlanarMetadataSegmentMarkers decider) := by
  let shape := directSourceFormulaShapeComputableInPolyTime decider
  let extract := FiniteBlockTransducer.computableInPolyTime
    retainedSegmentMarkerBlock
  let complete := TM2CompositionMachine.computableInPolyTime shape extract
  exact complete

end LeanTrominoes.PeriodicCNFStripReduction
