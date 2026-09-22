/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalPolarityClauseCoordinateHorizontalSemantics
import LeanTrominoes.UnaryPointFieldsCompiler

/-! # Native canonical clause-origin fields in actual incidence order -/
noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Computability Turing PeriodicOrthocrossing UnaryColumn
open PeriodicOneInThreePolarityNormalizationRouteSubdivision
variable {Input : Type} {encoding : _root_.Computability.FinEncoding Input} {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)
noncomputable local instance nativeClauseStackFintype (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack
local instance nativeClauseVariableDecidableEq : DecidableEq Variable := directSourceVariableDecidableEq

/-- One canonical origin per literal, retaining distinct clauses even when
positions coincide. This is the input column for literal-offset recovery. -/
def nativeIncidenceClausePositions (symbols : List encoding.Γ) : List Cell :=
  presentedIncidenceClausePositions
    (horizontalRoutedFormulaComputed (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols))
    (horizontalRoutedPlacementComputed (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols))

noncomputable def nativeIncidenceClauseFieldsCompilerOfInhabited [Inhabited encoding.Γ] :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (fun s => (nativeIncidenceClausePositions decider s).flatMap PeriodicGridDrawing.Arithmetic.pointFields) :=
  pointFieldsCompiler (rows := nativeIncidenceClausePositions decider) (point := fun _ p => p)
    (directSourceFinalHorizontalClauseCoordinatesComputableInPolyTime decider true true)
    (directSourceFinalHorizontalClauseCoordinatesComputableInPolyTime decider true false)
    (directSourceFinalHorizontalClauseCoordinatesComputableInPolyTime decider false true)
    (directSourceFinalHorizontalClauseCoordinatesComputableInPolyTime decider false false)

noncomputable def nativeIncidenceClauseFieldsCompiler :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (fun s => (nativeIncidenceClausePositions decider s).flatMap PeriodicGridDrawing.Arithmetic.pointFields) := by
  classical
  by_cases nonemptyAlphabet : Nonempty encoding.Γ
  · letI : Inhabited encoding.Γ := ⟨Classical.choice nonemptyAlphabet⟩
    exact nativeIncidenceClauseFieldsCompilerOfInhabited decider
  · letI : IsEmpty encoding.Γ := ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime UnaryFieldEncoderMachine.unaryFields _

end LeanTrominoes.PeriodicCNFStripReduction
end
