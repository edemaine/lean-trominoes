/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFigureNineCycleTailData
import LeanTrominoes.PeriodicCNFStripDirectFigureNinePolarityRouteTailRecordData
import LeanTrominoes.PeriodicCNFStripDirectRetainedFiniteSourceVariableMarkerCompiler
import LeanTrominoes.GadgetPreparedHeaderSemantics
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.RetainedInputAppendPipeline
import LeanTrominoes.TM2CompositionMachine

/-! # Compiler for the fixed Figure Seven cycle tail-record suffix -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing
open PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFigureNineCycleTailRecordCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFigureNineCycleTailRecordCompilerVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Replace each retained-variable marker by the constant flat record block
for one complete Figure Seven implication ring. -/
def directFigureNineCycleRouteTailRecordBlock :
    FormulaShapeDirectionOrdering.Token →
      List HorizontalRoutedRouteTailRecord.Token
  | .variable =>
      FormulaShapeRetainedFigureNineCycleTail.localRecordTokens
  | .clause _ => []

/-- Elementwise expansion of the already compiled retained-variable marker
stream. -/
def directFigureNineCycleRouteTailRecordTokensCompiled
    (symbols : List encoding.Γ) :
    List HorizontalRoutedRouteTailRecord.Token :=
  (directRetainedFigureNineFiniteSourceVariableMarkers
      decider symbols).flatMap
    directFigureNineCycleRouteTailRecordBlock

/-- The finite block expansion is exactly the semantic implication-cycle
tail-record suffix. -/
@[simp] theorem directFigureNineCycleRouteTailRecordTokensCompiled_eq
    (symbols : List encoding.Γ) :
    directFigureNineCycleRouteTailRecordTokensCompiled decider symbols =
      directFigureNineCycleRouteTailRecordTokens decider symbols := by
  let source := directSourceFormula decider symbols
  let atoms :=
    PeriodicThreeSATThree.sourceVariables
      (FormulaShapeRetainedFigureNineDirection.sourceScaledForFigureSeven
        source).erase
  unfold directFigureNineCycleRouteTailRecordTokensCompiled
    directRetainedFigureNineFiniteSourceVariableMarkers
    directFigureNineCycleRouteTailRecordBlock
  rw [GadgetPreparedHeaderEmitter.flatMap_replicate_apply]
  unfold directFigureNineCycleRouteTailRecordTokens
  rw [FormulaShapeRetainedFigureNineCycleTail.cycleRecordTokens_eq_finite]
  change
    (List.replicate atoms.length
      FormulaShapeRetainedFigureNineCycleTail.localRecordTokens).flatten =
      atoms.flatMap
        (fun _ => FormulaShapeRetainedFigureNineCycleTail.localRecordTokens)
  induction atoms with
  | nil => rfl
  | cons atom atoms induction =>
      simp only [List.length_cons, List.replicate_succ, List.flatten_cons,
        List.flatMap_cons, induction]

/-- The block expansion of retained-variable markers is polynomial-time
computable. -/
noncomputable def
    directFigureNineCycleRouteTailRecordTokensCompiledComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ)
      (List HorizontalRoutedRouteTailRecord.Token)
      encoding.Γ HorizontalRoutedRouteTailRecord.Token id id
      (directFigureNineCycleRouteTailRecordTokensCompiled decider) := by
  let markers :=
    directRetainedFigureNineFiniteSourceVariableMarkersComputableInPolyTime
      decider
  let records :=
    FiniteBlockTransducer.computableInPolyTime
      directFigureNineCycleRouteTailRecordBlock
  change @TM2ComputableInPolyTime
    (List encoding.Γ)
    (List HorizontalRoutedRouteTailRecord.Token)
    encoding.Γ HorizontalRoutedRouteTailRecord.Token id id
    (fun symbols =>
      (directRetainedFigureNineFiniteSourceVariableMarkers
        decider symbols).flatMap
          directFigureNineCycleRouteTailRecordBlock)
  exact TM2CompositionMachine.computableInPolyTime markers records

/-- The exact semantic implication-cycle tail-record suffix is
polynomial-time computable directly from source symbols. -/
noncomputable def
    directFigureNineCycleRouteTailRecordTokensComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ)
      (List HorizontalRoutedRouteTailRecord.Token)
      encoding.Γ HorizontalRoutedRouteTailRecord.Token id id
      (directFigureNineCycleRouteTailRecordTokens decider) :=
  RetainedInputAppendPipeline.computableInPolyTimeOfEq
    (directFigureNineCycleRouteTailRecordTokensCompiled decider)
    (directFigureNineCycleRouteTailRecordTokens decider)
    (directFigureNineCycleRouteTailRecordTokensCompiled_eq decider)
    (directFigureNineCycleRouteTailRecordTokensCompiledComputableInPolyTime
      decider)

end PeriodicCNFStripReduction
end LeanTrominoes

end
