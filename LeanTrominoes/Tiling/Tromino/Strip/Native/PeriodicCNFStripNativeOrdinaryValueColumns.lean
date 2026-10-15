/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Native.PeriodicCNFStripNativeOrdinaryProfiles
import LeanTrominoes.SAT.CNF.PeriodicCNFOrdinarySourceValueGeometry
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Atom.PeriodicCNFStripDirectSourceFinalAtomValueRowCodes
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Inherited.PeriodicCNFStripDirectSourceFinalInheritedCoordinateCompiler
import LeanTrominoes.Computation.Encoding.Unary.UnaryIndexedValueLookupCompiler

/-! # Native ordinary atom and position columns from inherited records -/
noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Turing PeriodicCNF PeriodicOrthocrossing
open PeriodicCNF.FormulaShapeDirectionOrdering PeriodicCNF.OrdinarySourceProjection
variable {Input : Type} {encoding : _root_.LeanTrominoes.FiniteEncoding Input} {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)
noncomputable local instance ordinaryValueStackFintype (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack
local instance ordinaryValueVariableDecidableEq : DecidableEq Variable := directSourceVariableDecidableEq
set_option maxHeartbeats 3000000

def nativeOrdinaryQueries (s : List encoding.Γ) : List Nat :=
  queries (directSourceFinalClauseDescriptors (PeriodicCNF.ProgramSource.ofDecider decider) s)

def nativeOrdinaryQueriesCompiler : TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
    (nativeOrdinaryQueries decider) := by
  unfold nativeOrdinaryQueries
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalClauseDescriptorsComputableInPolyTime (PeriodicCNF.ProgramSource.ofDecider decider)) OrdinarySourceProjection.compiler

private theorem orderedBlocks (s : List encoding.Γ) (blocks : List ValueBlock)
    (value : PeriodicLiteral OrdinaryVariable → Nat)
    (profiles : blocks.map (fun block => Token.clause block.1) = directSourceFinalClauseDescriptors (PeriodicCNF.ProgramSource.ofDecider decider) s)
    (literals : blocks.map (fun block => block.2.literals) =
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
        (directSourceFormula (PeriodicCNF.ProgramSource.ofDecider decider) s)).clauses.map (fun clause => clause.literals.map value)) :
    blocks.flatMap (fun block => orderedValues block.1 block.2.literals) =
      (nativeOrdinaryBaseInput decider s).1.clauses.flatMap (List.map value) := by
  have profileEq : blocks.map Prod.fst = nativeOrdinaryProfiles decider s := by
    rw [← directSourceFinalParentRouteBlocks_profiles] at profiles
    have h := congrArg (List.map (fun token => match token with
      | Token.clause profile => profile | Token.variable => default)) profiles
    simpa only [List.map_map, Function.comp_def, nativeOrdinaryProfiles] using h
  rw [orderedValueBlocks_eq, profileEq, literals]
  unfold nativeOrdinaryProfiles directSourceFinalParentRouteBlocks
  simp only [List.map_map, Function.comp_def]
  let source := retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula (directSourceFormula (PeriodicCNF.ProgramSource.ofDecider decider) s)
  have rows : source.clauses.map (fun clause => clause.literals.map value) =
      source.clauses.zipIdx.map (fun tagged => tagged.1.literals.map value) := by
    simpa only [List.map_map, Function.comp_def] using
      (congrArg (List.map (fun clause => clause.literals.map value)) (List.zipIdx_map_fst 0 source.clauses)).symm
  rw [rows, List.zipWith_map, List.zipWith_self, ← List.flatMap_def]
  change _ = ((PositionedPeriodicCNF.orderClausesByRouteDirection source
    (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes (directSourceFormula (PeriodicCNF.ProgramSource.ofDecider decider) s))).scale
      retainedFigureNineSourceClearanceFactor).erase.clauses.flatMap (List.map value)
  rw [PositionedPeriodicCNF.erase_scale]
  simp only [PositionedPeriodicCNF.erase, PositionedPeriodicCNF.orderClausesByRouteDirection, List.flatMap_map]
  apply List.flatMap_congr
  intro tagged member
  apply orderedValues_ofClause
  · exact retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula_clausesNonempty
      (directSourceFormula (PeriodicCNF.ProgramSource.ofDecider decider) s) (sourceFormula_clausesNonempty _) tagged.1
      (List.fst_mem_of_mem_zipIdx member)
  · exact retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula_widthAtMostThree
      (directSourceFormula (PeriodicCNF.ProgramSource.ofDecider decider) s) (sourceFormula_widthAtMostThree _) tagged.1.literals
      (PositionedPeriodicCNF.literals_mem_erase_of_mem_zipIdx member)

private def projectColumn [Inhabited encoding.Γ]
    (column : List encoding.Γ → List Nat)
    (blocks : List encoding.Γ → List ValueBlock)
    (value : List encoding.Γ → PeriodicLiteral OrdinaryVariable → Nat)
    (columnCompiler : TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields column)
    (columnEq : ∀ s, column s = (blocks s).flatMap valueBlock)
    (profiles : ∀ s, (blocks s).map (fun block => Token.clause block.1) = directSourceFinalClauseDescriptors (PeriodicCNF.ProgramSource.ofDecider decider) s)
    (literals : ∀ s, (blocks s).map (fun block => block.2.literals) =
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
        (directSourceFormula (PeriodicCNF.ProgramSource.ofDecider decider) s)).clauses.map (fun clause => clause.literals.map (value s))) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (fun s => (nativeOrdinaryBaseInput decider s).1.clauses.flatMap (List.map (value s))) := by
  let physical := UnaryIndexedValueLookup.valuesComputableInPolyTime id
    (nativeOrdinaryQueries decider) column (nativeOrdinaryQueriesCompiler decider) columnCompiler
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  rw [nativeOrdinaryQueries, columnEq, ← profiles s, lookupValues]
  exact orderedBlocks decider s (blocks s) (value s) (profiles s) (literals s)

def nativeOrdinaryAtomCodesCompiler [Inhabited encoding.Γ] :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields (nativeOrdinaryAtomCodes decider) := by
  apply TM2ComputableInPolyTime.of_eq (projectColumn decider
    (directSourceFinalInheritedRingAtomCodes (PeriodicCNF.ProgramSource.ofDecider decider)) (directSourceFinalAtomValueBlocks (PeriodicCNF.ProgramSource.ofDecider decider))
    (fun s literal => directSourceFinalRingVariableCode (PeriodicCNF.ProgramSource.ofDecider decider) s literal.atom)
    (directSourceFinalInheritedRingAtomCodesComputableInPolyTime (PeriodicCNF.ProgramSource.ofDecider decider))
    (directSourceFinalInheritedRingAtomCodes_eq_value_blocks (PeriodicCNF.ProgramSource.ofDecider decider))
    (directSourceFinalAtomValueBlocks_profiles (PeriodicCNF.ProgramSource.ofDecider decider)) (directSourceFinalAtomValueBlocks_literals (PeriodicCNF.ProgramSource.ofDecider decider)))
  intro s
  simp only [nativeOrdinaryAtomCodes, PeriodicCNF.variableOccurrences, List.map_flatMap, List.map_map, Function.comp_def]

def nativeOrdinaryPositionFieldsCompiler [Inhabited encoding.Γ] (horizontal positive : Bool) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (fun s => (nativeOrdinaryBaseInput decider s).1.clauses.flatMap (fun clause => clause.map (fun literal =>
        CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal positive)
          ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement (directSourceFormula (PeriodicCNF.ProgramSource.ofDecider decider) s)).position literal.atom)))) :=
  projectColumn decider (directSourceFinalInheritedCoordinates (PeriodicCNF.ProgramSource.ofDecider decider) horizontal positive)
    (directSourceFinalCoordinateValueBlocks (PeriodicCNF.ProgramSource.ofDecider decider) horizontal positive) _
    (directSourceFinalInheritedCoordinatesComputableInPolyTime (PeriodicCNF.ProgramSource.ofDecider decider) horizontal positive)
    (directSourceFinalInheritedCoordinates_eq_value_blocks (PeriodicCNF.ProgramSource.ofDecider decider) horizontal positive)
    (directSourceFinalCoordinateValueBlocks_profiles (PeriodicCNF.ProgramSource.ofDecider decider) horizontal positive)
    (directSourceFinalCoordinateValueBlocks_literals (PeriodicCNF.ProgramSource.ofDecider decider) horizontal positive)

end LeanTrominoes.PeriodicCNFStripReduction
end
