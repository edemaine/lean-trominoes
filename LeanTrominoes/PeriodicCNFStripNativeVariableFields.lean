/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFStripNativeAtomRenaming
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalPolarityVariableCoordinateHorizontalSemantics
import LeanTrominoes.UnaryColumnDedupCompiler
import LeanTrominoes.UnaryPointFieldsCompiler

/-! # Compiling actual variable positions in native incidence-vertex order -/
noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Computability Turing UnaryColumn PeriodicOrthocrossing
variable {Input : Type} {encoding : _root_.Computability.FinEncoding Input} {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)
noncomputable local instance nativeVariableStackFintype (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack
local instance nativeVariableDecidableEq : DecidableEq Variable := directSourceVariableDecidableEq
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 2000000

abbrev nativeAtoms (symbols : List encoding.Γ) := (nativeRoutedFormulaSource decider symbols).variableOccurrences

def nativeVariablePoint (symbols : List encoding.Γ) (atom : RoutedVariable) : Cell :=
  (horizontalRoutedPlacementComputed (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).position atom

def nativeVariablePositions (symbols : List encoding.Γ) : List Cell :=
  (nativeAtoms decider symbols).dedup.map (nativeVariablePoint decider symbols)

noncomputable def nativeAtomKeysCompiler :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (fun s => (nativeAtoms decider s).map (nativeAtomRenaming decider s)) := by
  exact TM2ComputableInPolyTime.of_eq (nativeRoutedFormulaAtomsComputableInPolyTime decider)
    (fun s => PeriodicCNF.variableOccurrences_rename _ _)

noncomputable def nativeVariableCoordinateCompiler [Inhabited encoding.Γ] (horizontal positive : Bool) :
    Compiler (fun s => (nativeAtoms decider s).dedup)
      (fun s a => CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal positive) (nativeVariablePoint decider s a)) :=
  UnaryColumn.dedup (nativeAtomKeysCompiler decider)
    (directSourceFinalHorizontalVariableCoordinatesComputableInPolyTime decider horizontal positive)
    (nativeAtomRenaming_injective decider)

noncomputable def nativeVariableFieldsCompilerOfInhabited [Inhabited encoding.Γ] :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (fun s => (nativeVariablePositions decider s).flatMap PeriodicGridDrawing.Arithmetic.pointFields) := by
  let result := pointFieldsCompiler
    (nativeVariableCoordinateCompiler decider true true)
    (nativeVariableCoordinateCompiler decider true false)
    (nativeVariableCoordinateCompiler decider false true)
    (nativeVariableCoordinateCompiler decider false false)
  exact TM2ComputableInPolyTime.of_eq result (fun s => by
    simp only [nativeVariablePositions,List.flatMap_map])

noncomputable def nativeVariableCountCompilerOfInhabited [Inhabited encoding.Γ] :
    ScalarCompiler (fun s => (nativeVariablePositions decider s).length) := by
  let result := countRows (dedupKeys (nativeAtomKeysCompiler decider) (nativeAtomRenaming_injective decider))
  exact TM2ComputableInPolyTime.of_eq result (fun s => by simp [nativeVariablePositions])

noncomputable def nativeVariableFieldsCompiler :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (fun s => (nativeVariablePositions decider s).flatMap PeriodicGridDrawing.Arithmetic.pointFields) := by
  classical
  by_cases nonemptyAlphabet : Nonempty encoding.Γ
  · letI : Inhabited encoding.Γ := ⟨Classical.choice nonemptyAlphabet⟩
    exact nativeVariableFieldsCompilerOfInhabited decider
  · letI : IsEmpty encoding.Γ := ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime UnaryFieldEncoderMachine.unaryFields _

noncomputable def nativeVariableCountCompiler :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (fun s => [(nativeVariablePositions decider s).length]) := by
  classical
  by_cases nonemptyAlphabet : Nonempty encoding.Γ
  · letI : Inhabited encoding.Γ := ⟨Classical.choice nonemptyAlphabet⟩
    exact nativeVariableCountCompilerOfInhabited decider
  · letI : IsEmpty encoding.Γ := ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime UnaryFieldEncoderMachine.unaryFields _

end LeanTrominoes.PeriodicCNFStripReduction
end
