/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseFanHorizontalSemantics

/-! # Polynomial-time emission of the actual horizontal clause endpoint data -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing
open PeriodicPlanarOneInThreeToThreeDM PlanarThreeDM

local instance horizontalClauseFieldsInhabited :
    Inhabited (ClauseRibbonFanData × X3CClauseTerminalGroup) :=
  ⟨(⟨false, fun _ => .north⟩, .top)⟩

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance horizontalClauseCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The actual horizontal fan stream, with one fan per routed clause. -/
def directSourceFinalHorizontalClauseFans (symbols : List encoding.Γ) :
    List ClauseRibbonFanData :=
  (List.range (horizontalRoutedFormulaComputed
    (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).clauses.length).map
      (fun index => horizontalOccurrenceClauseRibbonFanDataComputed
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols, index))

/-- The verified direct compiler emits the actual horizontal fan stream in
polynomial time, without a remaining semantic-agreement assumption. -/
noncomputable def directSourceFinalHorizontalClauseFansComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalHorizontalClauseFans decider) := by
  apply Turing.TM2ComputableInPolyTime.of_eq
    (directSourceFinalClauseFansComputableInPolyTime decider)
  intro symbols
  exact directSourceFinalClauseFans_eq_horizontal decider symbols

/-- Clause-side endpoint fields for every actual horizontal occurrence, in
clause-major and literal-minor order. -/
def directSourceFinalHorizontalClauseFrameFields (symbols : List encoding.Γ) :
    List (ClauseRibbonFanData × X3CClauseTerminalGroup) :=
  (horizontalRoutedFormulaComputed
    (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).clauses.zipIdx.flatMap
      (fun clause => (List.range clause.1.literals.length).map fun index =>
        (horizontalOccurrenceClauseRibbonFanDataComputed
          (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols, clause.2),
          terminalGroupOfLiteralIndex index))

/-- Projecting the finite direct frames therefore compiles all actual
horizontal clause endpoint fields in polynomial time. -/
noncomputable def directSourceFinalHorizontalClauseFrameFieldsComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalHorizontalClauseFrameFields decider) := by
  let compiled := TM2CompositionMachine.computableInPolyTime
    (directSourceFinalClauseFramesComputableInPolyTime decider)
    (FiniteBlockTransducer.computableInPolyTime
      (fun frame : HorizontalRoutedRouteHeaderClauseFrame.Data =>
        [(frame.clauseFan, frame.group)]))
  apply Turing.TM2ComputableInPolyTime.of_eq compiled
  intro symbols
  change (directSourceFinalClauseFrames decider symbols).flatMap
    (fun frame => [(frame.clauseFan, frame.group)]) = _
  rw [← List.map_eq_flatMap]
  exact directSourceFinalClauseFrames_fan_groups_eq_horizontal decider symbols

end LeanTrominoes.PeriodicCNFStripReduction

end
