/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionCircuitPaletteCompiler
import LeanTrominoes.GadgetSparseAssignmentColumnCompiler
import LeanTrominoes.UnaryColumnScalarCompiler
import LeanTrominoes.UnaryFieldUnitLengthBroadcastCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalVertexRecordCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalRouteRasterRequestCompiler
import LeanTrominoes.PeriodicCNFStripDirectSparseRecordAppenderCompiler
import LeanTrominoes.PeriodicCNFStripDirectPreparedHeaderEmitter

/-! # Actual polynomial-time source drawing columns for completion hardness -/
noncomputable section
namespace LeanTrominoes.CompletionPattern.Runtime
open Computability Turing UnaryColumn PeriodicCNFStripReduction
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
variable {Input : Type} {encoding : _root_.Computability.FinEncoding Input}
  {language : Input → Prop} (decider : Complexity.DeciderInPolySpace encoding language)

local instance sourceColumnStack (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack

abbrev sourceDrawing := directCompiledStripDrawingOfSymbols decider
abbrev sourceRows := directSparseAssignmentsOfSymbols decider

def sourceRecordCompiler : TM2ComputableInPolyTime id GadgetSparseAssignmentTokens.assignmentsTokens
    (sourceRows decider) := by
  let result := directSparseRecordEmitterOfAppenders decider
    (directSparseVertexRecordAppender decider) (directSparseRouteRecordAppender decider)
  apply TM2PolyTimeOutputEncodingTransport.of_identity_output_eq result
  intro s
  unfold sourceRows directSparseAssignmentRecordsOfSymbols
  rfl

def sourceXCompiler : Compiler (sourceRows decider) (fun _ a => a.1.1.toNat) :=
  TM2CompositionMachine.computableInPolyTime (sourceRecordCompiler decider)
    (GadgetSparseAssignmentColumns.coordinateCompiler false)

def sourceYCompiler : Compiler (sourceRows decider) (fun _ a => a.1.2.toNat) :=
  TM2CompositionMachine.computableInPolyTime (sourceRecordCompiler decider)
    (GadgetSparseAssignmentColumns.coordinateCompiler true)

def sourceKindCompiler : Compiler (sourceRows decider) (fun _ a => (kindIndex (LBricks.kindOf a.2)).val) :=
  TM2CompositionMachine.computableInPolyTime (sourceRecordCompiler decider)
    (GadgetSparseAssignmentColumns.typeCompiler (fun k => (kindIndex (LBricks.kindOf k)).val))

def sourceWidthCompiler : ScalarCompiler (fun s => (sourceDrawing decider s).horizontalPeriod) := by
  let units := directGridUnitsOfSymbolsComputableInPolyTime decider
  let count := TM2CompositionMachine.computableInPolyTime units UnaryFieldUnitLengthBroadcast.singletonComputableInPolyTime
  let result := TM2CompositionMachine.computableInPolyTime count
    (UnaryFieldConstantScale.computableInPolyTime normalizationPeriodFactor)
  apply TM2ComputableInPolyTime.of_eq result
  intro s
  simp only [UnaryFieldConstantScale.values,List.map_cons,List.map_nil]
  rw [directGridUnitsOfSymbols_length]
  unfold sourceDrawing directCompiledStripDrawingOfSymbols compiledStripDrawing
  rw [PeriodicThreeDM.NormalizationCompiler.compileStrip_horizontalPeriod,normalizationInput_finalNormalizationPeriod_eq]
  simp [Nat.mul_comm]

def sourceHeightCompiler [Inhabited encoding.Γ] :
    ScalarCompiler (fun s => (sourceDrawing decider s).verticalPeriod) := by
  let base : Compiler (fun _ : List encoding.Γ => [()])
      (fun s _ => (sourceDrawing decider s).horizontalPeriod) := sourceWidthCompiler decider
  let result := add (scale base 3) (constant base 1)
  apply TM2ComputableInPolyTime.of_eq result
  intro s
  change [(sourceDrawing decider s).horizontalPeriod*3+1] = [(sourceDrawing decider s).verticalPeriod]
  unfold sourceDrawing directCompiledStripDrawingOfSymbols compiledStripDrawing
  rw [PeriodicThreeDM.NormalizationCompiler.compileStrip_horizontalPeriod,
    PeriodicThreeDM.NormalizationCompiler.compileStrip_verticalPeriod]
  simp [PeriodicThreeDM.NormalizationCompiler.finalStripHeight,Nat.mul_comm]
end LeanTrominoes.CompletionPattern.Runtime
