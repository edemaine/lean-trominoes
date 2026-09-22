/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFStripNativeOffsetColumns
import LeanTrominoes.PeriodicCNFStripNativeRouteGeometry
import LeanTrominoes.PeriodicCNFStripNativePeriodCompiler
import LeanTrominoes.CanonicalLiteralOffsetCompiler
import LeanTrominoes.UnaryPointFieldsCompiler

/-! # Native fields of actual anchored literal offsets -/
noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Computability Turing UnaryColumn DelimitedDirectionDisplacement
variable {Input : Type} {encoding : _root_.Computability.FinEncoding Input} {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)
noncomputable local instance nativeLiteralOffsetStackFintype (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack
local instance nativeLiteralOffsetVariableDecidableEq : DecidableEq Variable := directSourceVariableDecidableEq
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 2048

noncomputable def nativeAnchoredOffsetCompilerOfInhabited [Inhabited encoding.Γ] (horizontal : Bool) :
    Compiler (nativeIncidenceRows decider) (fun _ row => Encodable.encode (component horizontal
      (Cell.sub row.2.1.offset (PeriodicCNF.clauseAnchor row.1.1.literals)))) := by
  apply canonicalLiteralOffsetCompiler (rows := nativeIncidenceRows decider) horizontal
    (fun s => horizontalRoutedPlacementComputed (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider s))
    (fun _ row => row.1.1) (fun _ row => row.2.1)
    (fun s row => horizontalRoutedRoutesComputed (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider s) row.1.2 row.2.2)
    (by simpa only [SignedUnaryCoordinateRefinement.field, Bool.false_eq_true, ↓reduceIte] using
      nativeOffsetClauseColumn decider horizontal true)
    (by simpa only [SignedUnaryCoordinateRefinement.field, Bool.false_eq_true, ↓reduceIte] using
      nativeOffsetClauseColumn decider horizontal false)
    (by simpa only [SignedUnaryCoordinateRefinement.field, Bool.false_eq_true, ↓reduceIte] using
      nativeOffsetDisplacementColumn decider horizontal true)
    (by simpa only [SignedUnaryCoordinateRefinement.field, Bool.false_eq_true, ↓reduceIte] using
      nativeOffsetDisplacementColumn decider horizontal false)
    (by simpa only [SignedUnaryCoordinateRefinement.field, Bool.false_eq_true, ↓reduceIte] using
      nativeOffsetVariableColumn decider horizontal true)
    (by simpa only [SignedUnaryCoordinateRefinement.field, Bool.false_eq_true, ↓reduceIte] using
      nativeOffsetVariableColumn decider horizontal false)
    (nativeRoutedPeriodCompiler decider)
    (fun s => nativeRoutedPeriod_positive _)
  · intro s row member
    have hm := (PositionedIncidenceRows.mem_rows
      (horizontalRoutedFormulaComputed (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider s)) row).mp member
    exact (nativeRoutedRoute_endpoints (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider s) hm.1 hm.2).1
  · intro s row member
    have hm := (PositionedIncidenceRows.mem_rows
      (horizontalRoutedFormulaComputed (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider s)) row).mp member
    exact (nativeRoutedRoute_endpoints (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider s) hm.1 hm.2).2
  · intro s row member
    have hm := (PositionedIncidenceRows.mem_rows
      (horizontalRoutedFormulaComputed (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider s)) row).mp member
    exact nativeRoutedRoute_unitSteps (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider s) hm.1 hm.2

/-- No remaining geometric assumptions or nonempty-alphabet requirement. -/
noncomputable def nativeAnchoredOffsetCompiler (horizontal : Bool) :
    Compiler (nativeIncidenceRows decider) (fun _ row => Encodable.encode (component horizontal
      (Cell.sub row.2.1.offset (PeriodicCNF.clauseAnchor row.1.1.literals)))) := by
  classical
  by_cases nonemptyAlphabet : Nonempty encoding.Γ
  · letI : Inhabited encoding.Γ := ⟨Classical.choice nonemptyAlphabet⟩
    exact nativeAnchoredOffsetCompilerOfInhabited decider horizontal
  · letI : IsEmpty encoding.Γ := ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime UnaryFieldEncoderMachine.unaryFields _

/-- The output fields are the literal offsets of the actual anchor-normalized
formula, in clause-major, literal-minor order. -/
noncomputable def nativeNormalizedFormulaOffsetCompiler (horizontal : Bool) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (fun s => (horizontalRoutedFormulaComputed
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider s)).erase.anchorNormalize.clauses.flatMap
          (fun clause => clause.map (fun literal => Encodable.encode (component horizontal literal.offset)))) := by
  let result := nativeAnchoredOffsetCompiler decider horizontal
  apply TM2ComputableInPolyTime.of_eq result
  intro s
  exact PositionedIncidenceRows.anchoredOffsets
    (horizontalRoutedFormulaComputed (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider s))
    (fun point => Encodable.encode (component horizontal point))

end LeanTrominoes.PeriodicCNFStripReduction
end
