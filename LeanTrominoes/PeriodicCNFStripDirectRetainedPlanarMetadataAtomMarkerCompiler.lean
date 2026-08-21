/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataAtomMarkerData
import LeanTrominoes.PeriodicCNFStripDirectSourceFormulaShapeCompiler
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.TM2CompositionMachine

/-! # Polynomial-time direct retained metadata source-atom markers -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directRetainedAtomMarkerCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The source-atom marker phase is polynomial time: run the existing guarded
formula-shape compiler, then apply a fixed token filter. -/
noncomputable def
    directRetainedPlanarMetadataAtomMarkersComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ)
      (List PeriodicCNF.FormulaShapeDirectionOrdering.Token)
      encoding.Γ PeriodicCNF.FormulaShapeDirectionOrdering.Token
      id id (directRetainedPlanarMetadataAtomMarkers decider) := by
  let shape := directSourceFormulaShapeComputableInPolyTime decider
  let extract := FiniteBlockTransducer.computableInPolyTime
    retainedAtomMarkerBlock
  let complete := TM2CompositionMachine.computableInPolyTime shape extract
  exact complete

end LeanTrominoes.PeriodicCNFStripReduction
