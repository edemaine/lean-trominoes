/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFStripNativeRoutePoints
import LeanTrominoes.PeriodicCNFStripNativeClausePoints
import LeanTrominoes.PeriodicCNFStripNativeVariableFields
import LeanTrominoes.UnaryFieldClosure

/-! # The complete ordered vertex table of the native incidence drawing -/
noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Computability Turing UnaryColumn PositionedPeriodicCNF DelimitedDirectionDisplacement
variable {Input : Type} {encoding : _root_.Computability.FinEncoding Input} {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)
noncomputable local instance nativeDrawingVertexStackFintype (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack
local instance nativeDrawingVertexVariableDecidableEq : DecidableEq Variable := directSourceVariableDecidableEq
set_option maxHeartbeats 400000

theorem nativeDrawingVertexPositions (s : List encoding.Γ) :
    (nativeRoutedDrawing decider s).vertexPositions =
      nativeVariablePositions decider s ++ nativeClausePositions decider s := by
  simp only [nativeRoutedDrawing, incidenceDrawing, incidenceVertexPositions,
    PeriodicCNF.incidenceVariableVertices, List.map_map, Function.comp_def,
    nativeVariablePositions, nativeAtoms, nativeRoutedFormulaSource,
    nativeClausePositions]
  rfl

def nativeDrawingVertexCoordinateCompiler [Inhabited encoding.Γ] (horizontal positive : Bool) :
    Compiler (fun s => (nativeRoutedDrawing decider s).vertexPositions)
      (fun _ point => SignedUnaryCoordinateRefinement.field positive (component horizontal point)) := by
  let physical := UnaryFieldClosure.appendCompiler id _ _
    (nativeVariableCoordinateCompiler decider horizontal positive)
    (nativeClauseCoordinateCompiler decider horizontal positive)
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  dsimp only
  rw [nativeDrawingVertexPositions, List.map_append]
  simp only [nativeVariablePositions, List.map_map, Function.comp_def]
  cases horizontal <;> cases positive <;> rfl

def nativeDrawingVertexFieldsCompilerOfInhabited [Inhabited encoding.Γ] :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields (fun s =>
      (nativeRoutedDrawing decider s).vertexPositions.flatMap PeriodicGridDrawing.Arithmetic.pointFields) :=
  pointFieldsCompiler (rows := fun s => (nativeRoutedDrawing decider s).vertexPositions) (point := fun _ p => p)
    (nativeDrawingVertexCoordinateCompiler decider true true) (nativeDrawingVertexCoordinateCompiler decider true false)
    (nativeDrawingVertexCoordinateCompiler decider false true) (nativeDrawingVertexCoordinateCompiler decider false false)

def nativeDrawingVertexFieldsCompiler :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields (fun s =>
      (nativeRoutedDrawing decider s).vertexPositions.flatMap PeriodicGridDrawing.Arithmetic.pointFields) := by
  classical
  by_cases nonemptyAlphabet : Nonempty encoding.Γ
  · letI : Inhabited encoding.Γ := ⟨Classical.choice nonemptyAlphabet⟩
    exact nativeDrawingVertexFieldsCompilerOfInhabited decider
  · letI : IsEmpty encoding.Γ := ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime UnaryFieldEncoderMachine.unaryFields _

def nativeDrawingVertexCountCompiler [Inhabited encoding.Γ] :
    ScalarCompiler (fun s => (nativeRoutedDrawing decider s).vertexPositions.length) :=
  countRows (nativeDrawingVertexCoordinateCompiler decider true true)

end LeanTrominoes.PeriodicCNFStripReduction
end
