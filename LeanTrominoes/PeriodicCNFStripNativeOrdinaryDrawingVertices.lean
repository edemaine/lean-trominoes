/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFStripNativeOrdinaryDrawingRoutes
import LeanTrominoes.UnaryColumnDedupCompiler
import LeanTrominoes.UnaryPointFieldsCompiler
import LeanTrominoes.UnaryFieldFirstBlockFilter

/-! # Native ordinary drawing vertices in their exact incidence order -/
noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Turing UnaryColumn PositionedPeriodicCNF DelimitedDirectionDisplacement UnaryFieldBooleanFilter
open PeriodicCNF.FormulaShapeDirectionOrdering
variable {Input : Type} {encoding : _root_.Computability.FinEncoding Input} {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)
noncomputable local instance ordinaryVertexStackFintype (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack
local instance ordinaryVertexVariableDecidableEq : DecidableEq Variable := directSourceVariableDecidableEq
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 2048

abbrev nativeOrdinaryAtoms (s : List encoding.Γ) := (nativeOrdinaryFormula decider s).erase.variableOccurrences

def nativeOrdinaryVariablePositions (s : List encoding.Γ) : List Cell :=
  (nativeOrdinaryAtoms decider s).dedup.map (nativeOrdinaryPlacement decider s).position

def nativeOrdinaryClausePositions (s : List encoding.Γ) : List Cell :=
  (nativeOrdinaryFormula decider s).clauses.map (canonicalClausePosition (nativeOrdinaryPlacement decider s))

def nativeOrdinaryVariableVertexColumn [Inhabited encoding.Γ] (horizontal positive : Bool) :
    Compiler (fun s => (nativeOrdinaryAtoms decider s).dedup) (fun s atom =>
      SignedUnaryCoordinateRefinement.field positive (component horizontal ((nativeOrdinaryPlacement decider s).position atom))) := by
  have keys : Compiler (nativeOrdinaryAtoms decider) (nativeOrdinaryRenaming decider) := by
    apply TM2ComputableInPolyTime.of_eq (nativeOrdinaryAtomCodesCompiler decider)
    intro s
    rw [← nativeOrdinaryRenaming_atoms, nativeOrdinaryBaseInput_formula]
  have values : Compiler (nativeOrdinaryAtoms decider) (fun s atom =>
      SignedUnaryCoordinateRefinement.field positive (component horizontal ((nativeOrdinaryPlacement decider s).position atom))) := by
    apply TM2ComputableInPolyTime.of_eq (nativeOrdinaryVariableColumn decider horizontal positive)
    intro s
    have h := congrArg (List.map (fun atom => SignedUnaryCoordinateRefinement.field positive
      (component horizontal ((nativeOrdinaryPlacement decider s).position atom))))
      (PositionedIncidenceRows.atoms (nativeOrdinaryFormula decider s))
    simpa only [List.map_map, Function.comp_def] using h
  exact UnaryColumn.dedup keys values (nativeOrdinaryRenaming_injective decider)

def nativeOrdinaryClauseFirstControlsCompiler : TM2ComputableInPolyTime id id (fun s =>
    (nativeOrdinaryFormula decider s).clauses.flatMap (fun clause => firstBlockControls clause.literals.length)) := by
  let physical := TM2CompositionMachine.computableInPolyTime (nativeOrdinaryProfilesCompiler decider)
    (FiniteBlockTransducer.computableInPolyTime (fun profile : DirectedClauseProfile =>
      firstBlockControls profile.orderedProfile.literals.length))
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  have shape := congrArg (List.flatMap (fun literals => firstBlockControls literals.length))
    (nativeOrdinaryProfiles_literals decider s)
  rw [nativeOrdinaryBaseInput_formula] at shape
  simpa only [List.flatMap_map, PeriodicCNF.ClauseProfileOccurrenceSplit.literalProfiles,
    List.length_map, PositionedPeriodicCNF.erase] using shape

def nativeOrdinaryClauseVertexColumn [Inhabited encoding.Γ] (horizontal positive : Bool) :
    Compiler (nativeOrdinaryClausePositions decider) (fun _ point =>
      SignedUnaryCoordinateRefinement.field positive (component horizontal point)) := by
  let physical := selectedValuesComputableInPolyTime id _ _ (nativeOrdinaryClauseFirstControlsCompiler decider)
    (nativeOrdinaryClauseColumn decider horizontal positive)
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  have repeated := congrArg (List.map (fun point => SignedUnaryCoordinateRefinement.field positive (component horizontal point)))
    (PositionedIncidenceRows.clausePositions (nativeOrdinaryFormula decider s) (nativeOrdinaryPlacement decider s))
  simp only [List.map_map, Function.comp_def,
    PeriodicOneInThreePolarityNormalizationRouteSubdivision.presentedIncidenceClausePositions,
    List.map_flatMap, List.map_replicate] at repeated
  rw [repeated]
  have selected := selectedValues_firstBlocks (nativeOrdinaryFormula decider s).clauses
    (fun clause => clause.literals.length)
    (fun clause => SignedUnaryCoordinateRefinement.field positive
      (component horizontal (canonicalClausePosition (nativeOrdinaryPlacement decider s) clause)))
    (fun clause member => List.length_pos_iff.mpr (nativeOrdinaryClauses_nonempty decider s clause member))
  simpa only [nativeOrdinaryClausePositions, List.map_map, Function.comp_def] using selected

theorem nativeOrdinaryDrawingVertexPositions (s : List encoding.Γ) :
    (nativeOrdinaryDrawing decider s).vertexPositions =
      nativeOrdinaryVariablePositions decider s ++ nativeOrdinaryClausePositions decider s := by
  simp only [nativeOrdinaryDrawing, incidenceDrawing, incidenceVertexPositions,
    PeriodicCNF.incidenceVariableVertices, List.map_map, Function.comp_def,
    nativeOrdinaryVariablePositions, nativeOrdinaryAtoms, nativeOrdinaryClausePositions]

def nativeOrdinaryDrawingVertexColumn [Inhabited encoding.Γ] (horizontal positive : Bool) :
    Compiler (fun s => (nativeOrdinaryDrawing decider s).vertexPositions) (fun _ point =>
      SignedUnaryCoordinateRefinement.field positive (component horizontal point)) := by
  let physical := UnaryFieldClosure.appendCompiler id _ _
    (nativeOrdinaryVariableVertexColumn decider horizontal positive)
    (nativeOrdinaryClauseVertexColumn decider horizontal positive)
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  dsimp only
  rw [nativeOrdinaryDrawingVertexPositions, List.map_append]
  simp only [nativeOrdinaryVariablePositions, List.map_map, Function.comp_def]

def nativeOrdinaryDrawingVertexFieldsCompiler [Inhabited encoding.Γ] :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields (fun s =>
      (nativeOrdinaryDrawing decider s).vertexPositions.flatMap PeriodicGridDrawing.Arithmetic.pointFields) :=
  pointFieldsCompiler (rows := fun s => (nativeOrdinaryDrawing decider s).vertexPositions) (point := fun _ point => point)
    (nativeOrdinaryDrawingVertexColumn decider true true) (nativeOrdinaryDrawingVertexColumn decider true false)
    (nativeOrdinaryDrawingVertexColumn decider false true) (nativeOrdinaryDrawingVertexColumn decider false false)

end LeanTrominoes.PeriodicCNFStripReduction
end
