/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFStripNativeDrawingVertices
import LeanTrominoes.PeriodicCNFStripNativeDrawingSegments
import LeanTrominoes.PeriodicCNFStripNativeFormulaCompiler
import LeanTrominoes.PeriodicDrawingFieldsCompiler
import LeanTrominoes.PeriodicPlanarSATEncodingCompiler

/-! # Complete native encoding of the routed formula and its supplied drawing -/
noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Computability Turing UnaryColumn
variable {Input : Type} {encoding : _root_.Computability.FinEncoding Input} {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)
noncomputable local instance nativePlanarEncodingStackFintype (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack
local instance nativePlanarEncodingVariableDecidableEq : DecidableEq Variable := directSourceVariableDecidableEq
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 2048

theorem nativeDrawingGridSize (s : List encoding.Γ) :
    (nativeRoutedDrawing decider s).gridSize =
      (horizontalRoutedPlacementComputed (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider s)).period := by
  simp only [nativeRoutedDrawing, PositionedPeriodicCNF.incidenceDrawing, PeriodicGridDrawing.gridSize]
  exact Nat.succ_pred_eq_of_pos (nativeRoutedPeriod_positive _)

def nativeDrawingGridSizeCompiler [Inhabited encoding.Γ] :
    ScalarCompiler (fun s => (nativeRoutedDrawing decider s).gridSize) :=
  TM2ComputableInPolyTime.of_eq (nativeRoutedPeriodCompiler decider)
    (fun s => congrArg List.singleton (nativeDrawingGridSize decider s).symm)

def nativeDrawingFieldsCompilerOfInhabited [Inhabited encoding.Γ] :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (fun s => PeriodicGridDrawing.Arithmetic.fields (nativeRoutedDrawing decider s)) :=
  PeriodicGridDrawing.NativeCompiler.fieldsCompiler (nativeRoutedDrawing decider)
    (nativeDrawingGridSizeCompiler decider) (nativeDrawingSegmentFieldsCompiler decider)
    (nativeDrawingVertexFieldsCompiler decider) (nativeDrawingTrailerCompiler decider)

def nativeDrawingFieldsCompiler :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (fun s => PeriodicGridDrawing.Arithmetic.fields (nativeRoutedDrawing decider s)) := by
  classical
  by_cases nonemptyAlphabet : Nonempty encoding.Γ
  · letI : Inhabited encoding.Γ := ⟨Classical.choice nonemptyAlphabet⟩
    exact nativeDrawingFieldsCompilerOfInhabited decider
  · letI : IsEmpty encoding.Γ := ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime UnaryFieldEncoderMachine.unaryFields _

/-- The normalized formula and its unchanged supplied incidence geometry. -/
def nativePlanarInput (s : List encoding.Γ) : PeriodicPlanarSAT.Input Nat :=
  (nativeNormalizedFormula decider s, nativeRoutedDrawing decider s)

/-- Every native binary field is included: formula, drawing header, segment table,
vertex table, and complete route table. Target-language promises are separate. -/
def nativePlanarEncodingCompiler :
    TM2ComputableInPolyTime id PeriodicPlanarSAT.FlatEncoding.finEncoding.encode (nativePlanarInput decider) := by
  classical
  by_cases nonemptyAlphabet : Nonempty encoding.Γ
  · letI : Inhabited encoding.Γ := ⟨Classical.choice nonemptyAlphabet⟩
    exact PeriodicPlanarSAT.FlatEncoding.encodingCompiler (input := nativePlanarInput decider)
      (nativeFormulaFieldsCompiler decider) (nativeDrawingFieldsCompiler decider)
  · letI : IsEmpty encoding.Γ := ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    letI : Inhabited PeriodicPlanarSAT.FlatEncoding.finEncoding.Γ := ⟨.bit0⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime PeriodicPlanarSAT.FlatEncoding.finEncoding.encode _

end LeanTrominoes.PeriodicCNFStripReduction
end
