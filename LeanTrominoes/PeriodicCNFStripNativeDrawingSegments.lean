/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFStripNativeDrawingRoutes
import LeanTrominoes.DelimitedDirectionSegmentFieldsCompiler

/-! # The complete native indexed-segment table of the routed SAT drawing -/
noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Computability Turing UnaryColumn DelimitedDirectionDisplacement
variable {Input : Type} {encoding : _root_.Computability.FinEncoding Input} {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)
noncomputable local instance nativeDrawingSegmentsStackFintype (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack
local instance nativeDrawingSegmentsVariableDecidableEq : DecidableEq Variable := directSourceVariableDecidableEq
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 2048

def nativeDrawingSegmentFieldsCompilerOfInhabited [Inhabited encoding.Γ] :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields (fun s =>
      (nativeRoutedDrawing decider s).indexedSegments.flatMap PeriodicGridDrawing.Arithmetic.segmentFields) := by
  let physical := segmentFieldsCompiler (nativeIncidenceRows decider)
    (nativeIncidencePointDirections decider) (nativeIncidencePointStart decider)
    (nativeIncidencePointDirectionsCompiler decider)
    (nativeOffsetClauseColumn decider true true) (nativeOffsetClauseColumn decider true false)
    (nativeOffsetClauseColumn decider false true) (nativeOffsetClauseColumn decider false false)
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  rw [← segmentTableFields_drawing, nativeDrawingEdgeRoutes]
  apply congrArg segmentTableFields
  exact List.map_congr_left (fun row member => nativeIncidencePointRoute_rebuild decider s row member)

def nativeDrawingSegmentFieldsCompiler :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields (fun s =>
      (nativeRoutedDrawing decider s).indexedSegments.flatMap PeriodicGridDrawing.Arithmetic.segmentFields) := by
  classical
  by_cases nonemptyAlphabet : Nonempty encoding.Γ
  · letI : Inhabited encoding.Γ := ⟨Classical.choice nonemptyAlphabet⟩
    exact nativeDrawingSegmentFieldsCompilerOfInhabited decider
  · letI : IsEmpty encoding.Γ := ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime UnaryFieldEncoderMachine.unaryFields _

end LeanTrominoes.PeriodicCNFStripReduction
end
