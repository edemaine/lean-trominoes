/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFStripNativeOrdinaryDrawingVertices
import LeanTrominoes.PeriodicCNFStripNativeOrdinaryFormulaCompiler
import LeanTrominoes.PeriodicDrawingFieldsCompiler
import LeanTrominoes.PeriodicPlanarSATEncodingCompiler
import LeanTrominoes.TM2EmptyAlphabetListInputCompiler

/-! # Complete native encoding for the ordinary local planar 1D SAT reduction -/
noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Turing UnaryColumn
variable {Input : Type} {encoding : _root_.Computability.FinEncoding Input} {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)
noncomputable local instance ordinaryEncodingStackFintype (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack
local instance ordinaryEncodingVariableDecidableEq : DecidableEq Variable := directSourceVariableDecidableEq
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 2048

theorem nativeOrdinaryDrawingGridSize (s : List encoding.Γ) :
    (nativeOrdinaryDrawing decider s).gridSize = (nativeOrdinaryPlacement decider s).period := by
  simp only [nativeOrdinaryDrawing, PositionedPeriodicCNF.incidenceDrawing, PeriodicGridDrawing.gridSize]
  exact Nat.succ_pred_eq_of_pos (nativeOrdinaryPeriod_positive decider s)

def nativeOrdinaryDrawingGridSizeCompiler [Inhabited encoding.Γ] :
    ScalarCompiler (fun s => (nativeOrdinaryDrawing decider s).gridSize) :=
  TM2ComputableInPolyTime.of_eq (nativeOrdinaryPeriodCompiler decider)
    (fun s => congrArg List.singleton (nativeOrdinaryDrawingGridSize decider s).symm)

def nativeOrdinaryDrawingFieldsCompiler [Inhabited encoding.Γ] :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (fun s => PeriodicGridDrawing.Arithmetic.fields (nativeOrdinaryDrawing decider s)) :=
  PeriodicGridDrawing.NativeCompiler.fieldsCompiler (nativeOrdinaryDrawing decider)
    (nativeOrdinaryDrawingGridSizeCompiler decider) (nativeOrdinaryDrawingSegmentFieldsCompiler decider)
    (nativeOrdinaryDrawingVertexFieldsCompiler decider) (nativeOrdinaryDrawingTrailerCompiler decider)

theorem nativeOrdinaryInput_drawing (s : List encoding.Γ) :
    (nativeOrdinaryInput decider s).2 = nativeOrdinaryDrawing decider s := by
  rfl

def nativeOrdinaryEncodingCompiler :
    TM2ComputableInPolyTime id PeriodicPlanarSAT.FlatEncoding.finEncoding.encode (nativeOrdinaryInput decider) := by
  classical
  by_cases nonemptyAlphabet : Nonempty encoding.Γ
  · letI : Inhabited encoding.Γ := ⟨Classical.choice nonemptyAlphabet⟩
    have drawingCompiler : TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
        (fun s => PeriodicGridDrawing.Arithmetic.fields (nativeOrdinaryInput decider s).2) :=
      TM2ComputableInPolyTime.of_eq (nativeOrdinaryDrawingFieldsCompiler decider)
        (fun s => congrArg PeriodicGridDrawing.Arithmetic.fields (nativeOrdinaryInput_drawing decider s).symm)
    exact PeriodicPlanarSAT.FlatEncoding.encodingCompiler (input := nativeOrdinaryInput decider)
      (nativeOrdinaryFormulaFieldsCompiler decider) drawingCompiler
  · letI : IsEmpty encoding.Γ := ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    letI : Inhabited PeriodicPlanarSAT.FlatEncoding.finEncoding.Γ := ⟨.bit0⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime PeriodicPlanarSAT.FlatEncoding.finEncoding.encode _

end LeanTrominoes.PeriodicCNFStripReduction
end
