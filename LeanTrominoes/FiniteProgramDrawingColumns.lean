/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteProgramCompletion
import LeanTrominoes.FiniteNormalizedDrawingPeriods
import LeanTrominoes.FiniteProgramTrominoRegionCompiler
import LeanTrominoes.GadgetSparseAssignmentColumnCompiler
import LeanTrominoes.UnaryColumnScalarCompiler
import LeanTrominoes.TM2EncodedFunctionOutput

/-! # Actual source machines for the finite completion drawing -/
noncomputable section
namespace LeanTrominoes.FiniteProgramCompletion
open _root_.Computability Turing UnaryColumn Gadget Gadget.PeriodicOrthogonalDrawing
open PeriodicCNF PeriodicCNFStripReduction CompletionPattern CompletionPattern.Runtime LBricks
open FiniteProgramSparseTrominoRegion PeriodicThreeDM.NormalizationCompiler
set_option maxHeartbeats 10000
variable {Source : Type} {encoding : FinEncoding Source} {language : Source → Prop}
variable (source : ProgramSource encoding language)
variable (zero : ∀ symbols,FiniteCNF.ZeroOffsets (source.formulaOfSymbols symbols))

private theorem drawing_periods (symbols : List encoding.Γ) :
    (drawing source zero symbols).horizontalPeriod=finalNormalizationPeriod (paddedInputs source symbols) ∧
    (drawing source zero symbols).verticalPeriod=3*finalNormalizationPeriod (paddedInputs source symbols)+1 := by
  rw [paddedInputs_eq_presentation source zero,finalNormalizationPeriod_inputOfPresentation]
  simpa only [drawing,PeriodicThreeDM.ContinuousPlanarPresentation.finitePad] using
    (presentation (source.formulaOfSymbols symbols)).finiteNormalizedDrawing_periods
    (problemZero source zero symbols) (endpointBounds source symbols)

private def gridCompiler [Inhabited encoding.Γ] : ScalarCompiler
    (fun symbols => (inputs source symbols).drawing.gridSize) := by
  let result := TM2CompositionMachine.computableInPolyTime
    (directDrawingGridUnitsOfSymbolsComputableInPolyTime source)
    UnaryFieldUnitLengthBroadcast.singletonComputableInPolyTime
  exact result.of_eq (fun symbols => congrArg (fun n : Nat => [n])
    (directDrawingGridUnitsOfSymbols_length source symbols))

def widthCompiler [Inhabited encoding.Γ] : ScalarCompiler
    (fun symbols => (drawing source zero symbols).horizontalPeriod) := by
  let base : Compiler (fun _ : List encoding.Γ => [()])
      (fun symbols _ => (inputs source symbols).drawing.gridSize) := gridCompiler source
  let result := scale (add (scale base 3) (constant base 1)) 1728
  apply result.of_eq
  intro symbols
  dsimp only
  rw [(drawing_periods source zero symbols).1]
  change [((inputs source symbols).drawing.gridSize*3+1)*1728]=
    [1728*(3*(inputs source symbols).drawing.gridSize+1)]
  simp only [Nat.mul_comm]

def heightCompiler [Inhabited encoding.Γ] : ScalarCompiler
    (fun symbols => (drawing source zero symbols).verticalPeriod) := by
  let width : Compiler (fun _ : List encoding.Γ => [()])
      (fun symbols _ => (drawing source zero symbols).horizontalPeriod) := widthCompiler source zero
  exact (add (scale width 3) (constant width 1)).of_eq (fun symbols => by
    simp only [(drawing_periods source zero symbols).1,(drawing_periods source zero symbols).2,
      List.map_cons,List.map_nil,Nat.mul_comm])

private def emittedAssignments [Inhabited encoding.Γ] : TM2ComputableInPolyTime id
    GadgetSparseAssignmentTokens.assignmentsTokens (assignments source) :=
  TM2PolyTimeOutputEncodingTransport.of_encoded_function id
    GadgetSparseAssignmentTokens.assignmentsTokens (assignments source)
    (assignmentTokensComputableInPolyTime source zero)

def xCompiler [Inhabited encoding.Γ] : Compiler (assignments source) (fun _ a => a.1.1.toNat) :=
  TM2CompositionMachine.computableInPolyTime (emittedAssignments source zero)
    (GadgetSparseAssignmentColumns.coordinateCompiler false)

def yCompiler [Inhabited encoding.Γ] : Compiler (assignments source) (fun _ a => a.1.2.toNat) :=
  TM2CompositionMachine.computableInPolyTime (emittedAssignments source zero)
    (GadgetSparseAssignmentColumns.coordinateCompiler true)

def kindCompiler [Inhabited encoding.Γ] : Compiler (assignments source)
    (fun _ a => (kindIndex (kindOf a.2)).val) :=
  TM2CompositionMachine.computableInPolyTime (emittedAssignments source zero)
    (GadgetSparseAssignmentColumns.typeCompiler (fun cell => (kindIndex (kindOf cell)).val))
end LeanTrominoes.FiniteProgramCompletion
