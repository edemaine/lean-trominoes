/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFStripNativeClauseArities
import LeanTrominoes.PeriodicCNFStripNativeIncidenceClauseFields
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMSourceArity
import LeanTrominoes.UnaryFieldFirstBlockFilter

/-! # One native drawing vertex per clause, preserving coincident positions -/
noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Computability Turing UnaryColumn UnaryFieldBooleanFilter
open PeriodicOneInThreePolarityNormalizationRouteSubdivision
variable {Input : Type} {encoding : _root_.Computability.FinEncoding Input} {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)
noncomputable local instance nativeClausePointStackFintype (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack
local instance nativeClausePointVariableDecidableEq : DecidableEq Variable := directSourceVariableDecidableEq
set_option maxHeartbeats 800000

def nativeClausePositions (s : List encoding.Γ) : List Cell :=
  (horizontalRoutedFormulaComputed (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider s)).clauses.map
    (PositionedPeriodicCNF.canonicalClausePosition
      (horizontalRoutedPlacementComputed (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider s)))

def nativeClauseFirstControlsCompiler : TM2ComputableInPolyTime id id (fun s =>
    (horizontalRoutedFormulaComputed (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider s)).clauses.flatMap
      (fun clause => firstBlockControls clause.literals.length)) := by
  let physical := TM2CompositionMachine.computableInPolyTime
    (directSourceFinalClauseDescriptorsComputableInPolyTime decider)
    (FiniteBlockTransducer.computableInPolyTime (fun token =>
      (HorizontalRoutedRouteHeaderClauseFrame.tokenBlocks token).flatMap
        (fun block => firstBlockControls block.length)))
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  have shape := congrArg (List.flatMap firstBlockControls) (nativeClauseArities_eq decider s)
  simpa only [HorizontalRoutedRouteHeaderClauseFrame.outputBlocks,
    PositionedPeriodicCNF.erase, List.flatMap_map, List.flatMap_assoc, List.map_map,
    Function.comp_def] using shape

private theorem clause_positive {V : Type*} (source : PositionedPeriodicCNF V)
    (arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree source.erase)
    (clause : PositionedPeriodicClause V) (member : clause ∈ source.clauses) : 0 < clause.literals.length := by
  have lengths := arity clause.literals (List.mem_map.mpr ⟨clause, member, rfl⟩)
  omega

private theorem routed_clause_positive (source : PeriodicCNF Nat)
    (clause : PositionedPeriodicClause RoutedVariable)
    (member : clause ∈ (horizontalRoutedFormulaComputed source).clauses) : 0 < clause.literals.length := by
  apply clause_positive (horizontalRoutedFormulaComputed source) _ clause member
  rw [horizontalRoutedFormulaComputed_eq_semanticData]
  exact horizontalSemanticRoutedFormula_arityTwoOrThreeComputed source

def nativeClauseCoordinateCompiler [Inhabited encoding.Γ] (horizontal positive : Bool) :
    Compiler (nativeClausePositions decider) (fun _ point =>
      SignedUnaryCoordinateRefinement.field positive (DelimitedDirectionDisplacement.component horizontal point)) := by
  let physical := selectedValuesComputableInPolyTime id _ _ (nativeClauseFirstControlsCompiler decider)
    (directSourceFinalHorizontalClauseCoordinatesComputableInPolyTime decider horizontal positive)
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  unfold directSourceFinalHorizontalClauseCoordinates
  have selected := selectedValues_firstBlocks
    (horizontalRoutedFormulaComputed (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider s)).clauses
    (fun c => c.literals.length)
    (fun c => SignedUnaryCoordinateRefinement.field positive (DelimitedDirectionDisplacement.component horizontal
      (PositionedPeriodicCNF.canonicalClausePosition
        (horizontalRoutedPlacementComputed (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider s)) c)))
    (routed_clause_positive _)
  cases horizontal <;> cases positive <;>
    simpa only [nativeClausePositions, presentedIncidenceClausePositions,
      List.map_flatMap, List.map_replicate, List.map_map, Function.comp_def,
      SignedUnaryCoordinateRefinement.field, DelimitedDirectionDisplacement.component,
      PeriodicOrthocrossing.coordinateFieldOfBools, PeriodicOrthocrossing.CarrierCrossingPointField.pointValue,
      PeriodicOrthocrossing.CarrierCrossingPointField.keepPositive,
      PeriodicOrthocrossing.CarrierCrossingPointField.horizontal,
      Bool.false_eq_true, ↓reduceIte] using selected

def nativeClauseFieldsCompilerOfInhabited [Inhabited encoding.Γ] :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields (fun s =>
      (nativeClausePositions decider s).flatMap PeriodicGridDrawing.Arithmetic.pointFields) :=
  pointFieldsCompiler (rows := nativeClausePositions decider) (point := fun _ p => p)
    (nativeClauseCoordinateCompiler decider true true) (nativeClauseCoordinateCompiler decider true false)
    (nativeClauseCoordinateCompiler decider false true) (nativeClauseCoordinateCompiler decider false false)

def nativeClauseFieldsCompiler :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields (fun s =>
      (nativeClausePositions decider s).flatMap PeriodicGridDrawing.Arithmetic.pointFields) := by
  classical
  by_cases nonemptyAlphabet : Nonempty encoding.Γ
  · letI : Inhabited encoding.Γ := ⟨Classical.choice nonemptyAlphabet⟩
    exact nativeClauseFieldsCompilerOfInhabited decider
  · letI : IsEmpty encoding.Γ := ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime UnaryFieldEncoderMachine.unaryFields _

end LeanTrominoes.PeriodicCNFStripReduction
end
