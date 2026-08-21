/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataSegmentAtomMarkerData
import LeanTrominoes.PeriodicCNFStripDirectSourceFormulaShapeCompiler
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.TM2CompositionMachine

/-! # Polynomial-time combined segment and atom markers -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directRetainedSegmentAtomMarkerCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

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
